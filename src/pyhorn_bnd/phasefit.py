"""PhaseFit: weaker closed-form synthesis for branching (ite/mod) loops.

Implements the design in docs/phasefit-branching-loop-solver-design.md.

Positioning: a second, lower-power synthesis strategy that targets loops whose
per-step updates contain ``ite``/``mod`` (FreqHorn's ``s_split_*`` family).
Uses a guess-then-validate approach: every candidate still passes through
MultiHoudini / checkFact / checkConsecution / checkQuery before acceptance.

Pipeline overview
-----------------
1. extract_guarded_branches  – flatten nested ite into (guard, pure update)
2. seed atoms                – reuse SeedMiner
3. per-branch closed forms   – affine / simple recurrence closed forms via sympy
4. guard_as_function_of_index – substitute closed forms, detect mono crossover
                               or periodic truth pattern
5. stitch_phases             – walk boundaries, re-anchor successive phases
6. assemble candidates       – per-phase interval lemmas + raw guard atoms
7. validate                  – MultiHoudini (caller responsibility)

This module produces candidate lemmas; the caller is expected to feed them
into MultiHoudini.run (or the existing seed-houdini / trace-houdini paths).
"""

from __future__ import annotations

import logging
from collections.abc import Mapping, Sequence
from dataclasses import dataclass
from typing import Any

import sympy as sp
import z3
from z3.z3util import get_vars

from .horn import HornProgram, HornRule
from .seedminer import CandidateMap, SeedMiner, SeedMiningResult

logger = logging.getLogger(__name__)

# Tunable bounds from the design sketch
DEFAULT_PHASE_BUDGET_K = 8
DEFAULT_P_MAX = 256
DEFAULT_MAX_NESTING = 8

# Exception types expected from best-effort z3<->sympy translation and
# symbolic solving of arbitrary (possibly unsupported) input -- caught
# explicitly rather than via a blind `except Exception`, so a genuine bug
# elsewhere (e.g. a TypeError from real broken logic) doesn't silently
# masquerade as "this expression just isn't affine" and vanish.
_SYMBOLIC_BESTEFFORT_EXC = (
    TypeError,
    ValueError,
    ZeroDivisionError,
    NotImplementedError,
    AttributeError,
    sp.SympifyError,
    sp.PolynomialError,
    z3.Z3Exception,
)


# ---------------------------------------------------------------------------
# Data structures
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class GuardedUpdate:
    """One leaf of a flattened ite-tree for a single variable."""

    guard: z3.BoolRef          # conjunction of path conditions (may be True)
    update: z3.ExprRef         # ite-free expression over pre-state vars
    var: z3.ExprRef            # the post-state variable this defines


@dataclass
class Branch:
    """A simultaneous pure update for several variables under a common guard."""

    guard: z3.BoolRef
    updates: dict[z3.ExprRef, z3.ExprRef]  # post_var -> pure expr in pre vars
    # Optional name for debugging
    label: str = ""


@dataclass
class ClosedForm:
    """Symbolic closed form of a variable as a function of the loop index n."""

    var: z3.ExprRef                 # original program variable (canonical)
    # sympy expression in free symbols: n, and the initial-value symbols
    expr: sp.Expr
    # mapping from sympy initial symbols back to Z3 expressions (or free reals)
    init_map: dict[sp.Symbol, z3.ExprRef]
    # optional period if the form is known periodic
    period: int | None = None


@dataclass
class PhaseBoundary:
    """A discovered phase transition point."""

    n_star: int | sp.Expr           # concrete integer or symbolic crossover
    from_branch: int
    to_branch: int
    reason: str                     # "monotonic" | "periodic" | ...


@dataclass
class Phase:
    """One contiguous regime of the loop."""

    index: int
    branch: Branch
    start_n: int | sp.Expr          # inclusive lower bound on n
    end_n: int | sp.Expr | None     # exclusive upper, or None = unbounded
    closed_forms: dict[z3.ExprRef, ClosedForm]
    # the symbolic state at the start of this phase (for re-anchoring)
    init_state: dict[z3.ExprRef, z3.ExprRef]


@dataclass
class PhaseFitResult:
    """Output of a PhaseFit run for one inductive rule / relation."""

    relation: z3.FuncDeclRef
    phases: list[Phase]
    boundaries: list[PhaseBoundary]
    candidates: list[z3.BoolRef]    # assembled interval lemmas + guard atoms
    success: bool
    message: str = ""


# ---------------------------------------------------------------------------
# 1. extract_guarded_branches
# ---------------------------------------------------------------------------

def _is_ite(e: z3.ExprRef) -> bool:
    return z3.is_app(e) and e.decl().kind() == z3.Z3_OP_ITE


def _flatten_ite(
    expr: z3.ExprRef,
    path_guard: z3.BoolRef | None = None,
    max_depth: int = DEFAULT_MAX_NESTING,
) -> list[tuple[z3.BoolRef, z3.ExprRef]]:
    """Recursively flatten nested If into a list of (guard, leaf_expr).

    Also pushes flattening through arithmetic operators (+, -, *) so that
    an expression such as ``1 + If(c, a, b)`` is split into the two leaves
    ``(c, 1+a)`` and ``(Not(c), 1+b)``.
    """
    if path_guard is None:
        path_guard = z3.BoolVal(True)

    if max_depth <= 0:
        return [(path_guard, expr)]

    if _is_ite(expr):
        cond = expr.arg(0)
        then_e = expr.arg(1)
        else_e = expr.arg(2)
        then_guard = z3.And(path_guard, cond) if not z3.is_true(path_guard) else cond
        else_guard = z3.And(path_guard, z3.Not(cond)) if not z3.is_true(path_guard) else z3.Not(cond)
        results: list[tuple[z3.BoolRef, z3.ExprRef]] = []
        results.extend(_flatten_ite(then_e, then_guard, max_depth - 1))
        results.extend(_flatten_ite(else_e, else_guard, max_depth - 1))
        return results

    # Push through unary minus
    if z3.is_app(expr) and expr.decl().kind() == z3.Z3_OP_UMINUS:
        sub = _flatten_ite(expr.arg(0), path_guard, max_depth - 1)
        return [(g, -u) for g, u in sub]

    # Push through binary arithmetic that may contain ites in arguments
    if z3.is_add(expr) or z3.is_sub(expr) or z3.is_mul(expr):
        kids = list(expr.children())
        # Flatten each child; if any child yields >1 leaf, distribute
        child_leaves = [_flatten_ite(k, z3.BoolVal(True), max_depth - 1) for k in kids]
        if all(len(cl) == 1 for cl in child_leaves):
            # no ite underneath – keep as is
            return [(path_guard, expr)]
        # Distribute: Cartesian product of child leaves, rebuild the op
        from itertools import product
        results = []
        for combo in product(*child_leaves):
            gs = [g for g, _ in combo]
            us = [u for _, u in combo]
            non_true = [gg for gg in gs if not z3.is_true(gg)]
            g = z3.And(path_guard, *non_true) if non_true else path_guard
            if z3.is_add(expr):
                new_e = sum(us[1:], us[0]) if us else z3.IntVal(0)
            elif z3.is_sub(expr):
                new_e = us[0]
                for uu in us[1:]:
                    new_e = new_e - uu
            else:  # mul
                new_e = us[0]
                for uu in us[1:]:
                    new_e = new_e * uu
            results.append((g, new_e))
        return results

    return [(path_guard, expr)]


def _collect_equalities(body: z3.BoolRef) -> list[tuple[z3.ExprRef, z3.ExprRef]]:
    """Extract top-level equality conjuncts from a rule body."""
    eqs: list[tuple[z3.ExprRef, z3.ExprRef]] = []
    if z3.is_and(body):
        conjuncts = body.children()
    else:
        conjuncts = [body]
    for c in conjuncts:
        if z3.is_eq(c):
            eqs.append((c.arg(0), c.arg(1)))
    return eqs


def _fully_expand(
    expr: z3.ExprRef,
    defs: dict[int, z3.ExprRef],
    src_ids: set[int],
    depth: int = 16,
) -> z3.ExprRef:
    """Repeatedly substitute intermediate definitions until only src vars remain."""
    if depth <= 0:
        return expr
    changed = False
    free = get_vars(expr)
    for v in free:
        vid = v.get_id()
        if vid in defs and vid not in src_ids:
            try:
                expr = z3.substitute(expr, (v, defs[vid]))
                changed = True
            except z3.Z3Exception:
                pass
    if changed:
        return _fully_expand(expr, defs, src_ids, depth - 1)
    return expr


def extract_guarded_branches(
    rule: HornRule,
    *,
    per_variable: bool = True,
) -> list[Branch]:
    """Flatten nested ite() appearing in the transition equalities of *rule*.

    Returns a list of Branch objects.  When *per_variable* is True each
    variable's ite-tree is considered independently and branches are the
    Cartesian product of the individual leaf guards (the common case for
    the s_split_* family).  When False, only the global conjunction of all
    active guards is used (synchronized).

    Only inductive rules (src == dst relation) are meaningful; others
    return an empty list.
    """
    if not rule.is_inductive or rule.src_relation is None:
        return []

    eqs = _collect_equalities(rule.body)
    # Map every defined variable (intermediate or final) to its RHS.
    defs_by_id: dict[int, z3.ExprRef] = {}
    for lhs, rhs in eqs:
        defs_by_id[lhs.get_id()] = rhs

    src_ids = {v.get_id() for v in rule.src_args}

    # Fully expand every dst_arg definition so it is expressed only in terms
    # of src_args (and constants / flag etc.).
    var_leaves: dict[z3.ExprRef, list[tuple[z3.BoolRef, z3.ExprRef]]] = {}
    for dst in rule.dst_args:
        if dst.get_id() in defs_by_id:
            pure = _fully_expand(defs_by_id[dst.get_id()], defs_by_id, src_ids)
            leaves = _flatten_ite(pure)
            cleaned: list[tuple[z3.BoolRef, z3.ExprRef]] = []
            for g, u in leaves:
                u2 = _fully_expand(u, defs_by_id, src_ids)
                g2 = _fully_expand(g, defs_by_id, src_ids) if z3.is_app(g) else g
                cleaned.append((g2, u2))
            var_leaves[dst] = cleaned
        else:
            try:
                # NOTE: use get_id()-based matching, not list.index() (i.e.
                # not `==`) -- dst_args can mix sorts (Int/Array/Bool/...),
                # and Z3's `__eq__` *raises* Z3Exception on a genuine sort
                # mismatch instead of returning False, so `.index()` would
                # crash while scanning past an earlier, differently-sorted
                # element instead of just skipping it.
                idx = next(
                    i
                    for i, a in enumerate(rule.dst_args)
                    if a.get_id() == dst.get_id()
                )
                src = rule.src_args[idx]
                var_leaves[dst] = [(z3.BoolVal(True), src)]
            except (StopIteration, IndexError):
                var_leaves[dst] = [(z3.BoolVal(True), dst)]

    if not var_leaves:
        return []

    if per_variable:
        from itertools import product
        keys = list(var_leaves.keys())
        leaf_lists = [var_leaves[k] for k in keys]
        total = 1
        for lst in leaf_lists:
            total *= max(len(lst), 1)
        if total > 64:
            logger.warning(
                "PhaseFit: Cartesian product of %d leaves too large; "
                "truncating to first leaf per variable",
                total,
            )
            leaf_lists = [
                [lst[0]] if lst else [(z3.BoolVal(True), k)]
                for k, lst in zip(keys, leaf_lists)
            ]

        branches: list[Branch] = []
        for combo in product(*leaf_lists):
            guards = [g for g, _ in combo]
            updates = {k: u for k, (_, u) in zip(keys, combo)}
            non_true = [gg for gg in guards if not z3.is_true(gg)]
            # De-duplicate identical guard conjuncts -- a common case is
            # several variables sharing the same top-level ite condition,
            # which otherwise produces pointless repeats like
            # And(p, p, p) instead of just p.
            seen_guards: set[str] = set()
            deduped: list[z3.BoolRef] = []
            for gg in non_true:
                key = gg.sexpr()
                if key not in seen_guards:
                    seen_guards.add(key)
                    deduped.append(gg)
            g = z3.And(*deduped) if deduped else z3.BoolVal(True)
            s = z3.Solver()
            s.set("timeout", 80)
            s.add(g)
            if s.check() == z3.unsat:
                continue
            branches.append(Branch(guard=g, updates=updates))
        seen: set[str] = set()
        unique: list[Branch] = []
        for b in branches:
            key = str(sorted((str(k), str(v)) for k, v in b.updates.items()))
            if key not in seen:
                seen.add(key)
                unique.append(b)
        return unique
    else:
        return extract_guarded_branches(rule, per_variable=True)


# ---------------------------------------------------------------------------
# 3. per-branch closed forms (simple affine via sympy)
# ---------------------------------------------------------------------------

def _z3_to_sympy(e: z3.ExprRef, symbol_map: dict[int, sp.Symbol]) -> sp.Expr:
    """Best-effort conversion of a linear/affine Z3 expression to sympy.

    Raises ValueError if *e* still contains an ``ite`` that survived
    flattening (e.g. nested inside a ``mod``/``div``, which
    ``_flatten_ite`` does not push through) -- such an expression must not
    be silently treated as an opaque free variable, since that would make
    the resulting "closed form" look successfully affine while actually
    ignoring a branch.
    """
    if _is_ite(e):
        raise ValueError(f"unflattened ite reached _z3_to_sympy: {e}")
    if z3.is_int_value(e) or z3.is_rational_value(e) or z3.is_algebraic_value(e):
        return sp.Integer(e.as_long()) if e.is_int() else sp.Rational(str(e))
    if z3.is_true(e):
        return sp.true
    if z3.is_false(e):
        return sp.false
    if z3.is_const(e) and e.get_id() in symbol_map:
        return symbol_map[e.get_id()]
    if z3.is_add(e):
        return sum((_z3_to_sympy(a, symbol_map) for a in e.children()), sp.Integer(0))
    if z3.is_mul(e):
        res = sp.Integer(1)
        for a in e.children():
            res *= _z3_to_sympy(a, symbol_map)
        return res
    if z3.is_sub(e):
        kids = e.children()
        return _z3_to_sympy(kids[0], symbol_map) - sum(
            _z3_to_sympy(a, symbol_map) for a in kids[1:]
        )
    if z3.is_app(e) and e.decl().kind() == z3.Z3_OP_UMINUS:
        return -_z3_to_sympy(e.arg(0), symbol_map)
    # mod
    if z3.is_app(e) and e.decl().kind() == z3.Z3_OP_MOD:
        return sp.Mod(_z3_to_sympy(e.arg(0), symbol_map), _z3_to_sympy(e.arg(1), symbol_map))
    # fallback: treat as a free symbol
    sid = e.get_id()
    if sid not in symbol_map:
        symbol_map[sid] = sp.Symbol(f"v{sid}", integer=True)
    return symbol_map[sid]


def compute_closed_form(
    update: z3.ExprRef,
    var: z3.ExprRef,
    pre_vars: Sequence[z3.ExprRef],
    init_values: Mapping[z3.ExprRef, z3.ExprRef] | None = None,
) -> ClosedForm | None:
    """Compute a closed form for a single variable under a pure (ite-free) update.

    Supports:
    - x' = x + c          →  x0 + c*n
    - x' = a*x + b        →  geometric closed form (a constant)
    - x' = c              →  constant
    - x' = (x + 1) mod m  →  (x0 + n) mod m   (special-cased)

    Returns None when the update is not recognised as a simple affine
    recurrence that sympy (or the special cases) can solve.
    """
    n = sp.Symbol("n", integer=True, nonnegative=True)
    symbol_map: dict[int, sp.Symbol] = {}

    # Map pre-state variables to sympy symbols; the target var gets a special
    # initial-value symbol.
    x0_sym = sp.Symbol(f"{var}_0", integer=True)
    for v in pre_vars:
        if v.get_id() == var.get_id():
            symbol_map[v.get_id()] = x0_sym
        else:
            symbol_map[v.get_id()] = sp.Symbol(str(v), integer=True)

    # Also map any free constants that appear
    for v in get_vars(update):
        if v.get_id() not in symbol_map:
            symbol_map[v.get_id()] = sp.Symbol(str(v), integer=True)

    try:
        rhs_sp = _z3_to_sympy(update, symbol_map)
    except _SYMBOLIC_BESTEFFORT_EXC as exc:
        logger.debug("z3→sympy failed for %s: %s", update, exc)
        return None

    # Special case: identity
    if rhs_sp == x0_sym:
        init_map = {x0_sym: init_values.get(var, var) if init_values else var}
        return ClosedForm(var=var, expr=x0_sym, init_map=init_map)

    # Special case: constant
    if x0_sym not in rhs_sp.free_symbols:
        init_map = {x0_sym: init_values.get(var, var) if init_values else var}
        return ClosedForm(var=var, expr=rhs_sp, init_map=init_map)

    # Special case: (x + c) mod m
    if isinstance(rhs_sp, sp.Mod):
        arg, mod = rhs_sp.args
        if arg.has(x0_sym) and not mod.has(x0_sym):
            # assume arg = x0 + c
            c = sp.simplify(arg - x0_sym)
            if c.is_constant():
                expr = sp.Mod(x0_sym + c * n, mod)
                init_map = {x0_sym: init_values.get(var, var) if init_values else var}
                try:
                    period = int(mod)
                except _SYMBOLIC_BESTEFFORT_EXC:
                    period = None
                return ClosedForm(var=var, expr=expr, init_map=init_map, period=period)

    # Linear recurrence x' = a*x + b
    # Collect coefficient of x0_sym and the rest
    try:
        poly = sp.Poly(rhs_sp, x0_sym)
        if poly.degree() > 1:
            return None
        a = poly.coeff_monomial(x0_sym) if poly.degree() == 1 else sp.Integer(0)
        b = poly.coeff_monomial(1)
    except _SYMBOLIC_BESTEFFORT_EXC:
        # not a polynomial in x0
        return None

    # Solve the recurrence with sympy.rsolve
    f = sp.Function("f")
    rec = f(n + 1) - a * f(n) - b
    try:
        sol = sp.rsolve(rec, f(n), [f(0)])
        if sol is None:
            return None
        # sol is an expression in f(0) and n; replace f(0) by x0_sym
        sol = sol.subs(f(0), x0_sym)
        sol = sp.simplify(sol)
    except _SYMBOLIC_BESTEFFORT_EXC as exc:
        logger.debug("rsolve failed: %s", exc)
        # Fallback for a == 1: x0 + b*n
        if a == 1:
            sol = x0_sym + b * n
        elif a == 0:
            sol = b
        else:
            return None

    init_map = {x0_sym: init_values.get(var, var) if init_values else var}
    # Also keep any other free symbols that appear in b
    for s in sol.free_symbols:
        if s != n and s != x0_sym and s not in init_map:
            # try to recover a Z3 expression
            for zid, ssym in symbol_map.items():
                if ssym == s:
                    # find the Z3 var
                    for v in pre_vars:
                        if v.get_id() == zid:
                            init_map[s] = init_values.get(v, v) if init_values else v
                            break
                    break

    return ClosedForm(var=var, expr=sol, init_map=init_map)


def compute_branch_closed_forms(
    branch: Branch,
    pre_vars: Sequence[z3.ExprRef],
    post_to_pre: Mapping[z3.ExprRef, z3.ExprRef],
    init_state: Mapping[z3.ExprRef, z3.ExprRef] | None = None,
) -> dict[z3.ExprRef, ClosedForm]:
    """Compute closed forms for every variable under a pure branch update.

    *post_to_pre* maps each post-state variable to the corresponding
    pre-state (canonical) variable so that the ClosedForm is keyed by the
    program variable the invariant will talk about.
    """
    forms: dict[z3.ExprRef, ClosedForm] = {}
    for post_v, upd in branch.updates.items():
        pre_v = post_to_pre.get(post_v, post_v)
        cf = compute_closed_form(upd, pre_v, pre_vars, init_state)
        if cf is not None:
            forms[pre_v] = cf
    return forms


# ---------------------------------------------------------------------------
# 4. guard_as_function_of_index
# ---------------------------------------------------------------------------

def _guard_to_sympy(
    guard: z3.BoolRef,
    closed_forms: Mapping[z3.ExprRef, ClosedForm],
    n_sym: sp.Symbol,
) -> sp.Expr | None:
    """Substitute closed forms into a guard atom and return a sympy predicate
    in n (and possibly other free symbols).
    """
    # Very simple: only handle comparisons of the form  t1  OP  t2
    # where OP is <, <=, >, >=, ==, != and t1/t2 become functions of n.
    if not z3.is_app(guard):
        return None
    kind = guard.decl().kind()
    op_map = {
        z3.Z3_OP_LT: sp.Lt,
        z3.Z3_OP_LE: sp.Le,
        z3.Z3_OP_GT: sp.Gt,
        z3.Z3_OP_GE: sp.Ge,
        z3.Z3_OP_EQ: sp.Eq,
        z3.Z3_OP_DISTINCT: lambda a, b: sp.Ne(a, b),
    }
    if kind not in op_map:
        # try to decompose And/Or of atoms
        if z3.is_and(guard):
            parts = []
            for c in guard.children():
                p = _guard_to_sympy(c, closed_forms, n_sym)
                if p is None:
                    return None
                parts.append(p)
            return sp.And(*parts)
        if z3.is_or(guard):
            parts = []
            for c in guard.children():
                p = _guard_to_sympy(c, closed_forms, n_sym)
                if p is None:
                    return None
                parts.append(p)
            return sp.Or(*parts)
        if z3.is_not(guard):
            p = _guard_to_sympy(guard.arg(0), closed_forms, n_sym)
            return sp.Not(p) if p is not None else None
        return None

    if guard.num_args() != 2:
        return None

    def term_to_sp(t: z3.ExprRef) -> sp.Expr | None:
        # Replace each free variable by its closed form (or leave free)
        free = get_vars(t)
        symbol_map: dict[int, sp.Symbol] = {}
        # First convert the term treating vars as symbols
        for v in free:
            if v in closed_forms:
                # we will substitute the closed-form expression later
                symbol_map[v.get_id()] = sp.Symbol(f"tmp_{v.get_id()}", integer=True)
            else:
                symbol_map[v.get_id()] = sp.Symbol(str(v), integer=True)
        try:
            s = _z3_to_sympy(t, symbol_map)
        except _SYMBOLIC_BESTEFFORT_EXC:
            return None
        # Now replace the temporary symbols by the closed-form exprs
        for v in free:
            if v in closed_forms:
                tmp = symbol_map[v.get_id()]
                cf = closed_forms[v]
                # substitute the init symbols of cf as well? keep them free
                s = s.subs(tmp, cf.expr)
        return sp.simplify(s)

    left = term_to_sp(guard.arg(0))
    right = term_to_sp(guard.arg(1))
    if left is None or right is None:
        return None
    return op_map[kind](left, right)


def _sympy_as_bool(expr: Any) -> bool | None:
    """Safely interpret a SymPy expression as a Python bool, or None if undecided.

    Relational objects raise TypeError under ``bool()`` / ``if`` / ``not``, so
    we never call those.  Equality against True/False/sp.true/sp.false is safe
    and is the idiomatic way to recognise BooleanTrue / BooleanFalse after
    simplification or concrete substitution.
    """
    if expr is True or expr is sp.true or expr == True or expr == sp.true:
        return True
    if expr is False or expr is sp.false or expr == False or expr == sp.false:
        return False
    # Last-chance simplify (e.g. Eq(x, x) -> True, or concrete arithmetic)
    try:
        s = sp.simplify(expr)
        if s is True or s is sp.true or s == True or s == sp.true:
            return True
        if s is False or s is sp.false or s == False or s == sp.false:
            return False
    except _SYMBOLIC_BESTEFFORT_EXC:
        pass
    return None


def classify_guard(
    guard: z3.BoolRef,
    closed_forms: Mapping[z3.ExprRef, ClosedForm],
    *,
    p_max: int = DEFAULT_P_MAX,
) -> tuple[str, Any]:
    """Classify a guard after substitution of closed forms.

    Returns one of:
      ("monotonic", n_star)   – single crossover at integer n_star
      ("periodic", period)    – truth pattern repeats with given period
      ("constant", bool)      – always true or always false
      ("unknown", None)       – cannot classify
    """
    n = sp.Symbol("n", integer=True, nonnegative=True)
    pred = _guard_to_sympy(guard, closed_forms, n)
    if pred is None:
        return ("unknown", None)

    def _truth_at(i: int) -> bool | None:
        try:
            val = pred.subs(n, i)
        except (TypeError, ValueError) as exc:
            logger.debug("classify_guard: eval at n=%s failed: %s", i, exc)
            return None
        return _sympy_as_bool(val)

    # Constant?
    const = _sympy_as_bool(pred)
    if const is not None:
        return ("constant", const)

    # Try to solve pred's change of truth value – look for roots of the
    # boundary equation of the comparison, then confirm the truth value
    # actually flips there (a root of "lhs == rhs" is not automatically a
    # sign change, and a "crossover" at n=0 would just mean the guard was
    # already false the moment this phase began, which is not a usable
    # interior boundary).
    try:
        eqs = []
        if isinstance(pred, (sp.StrictLessThan, sp.LessThan,
                             sp.StrictGreaterThan, sp.GreaterThan,
                             sp.Equality)):
            eqs.append(sp.Eq(pred.lhs, pred.rhs))
        for eq in eqs:
            try:
                sols = sp.solve(eq, n)
            except (TypeError, ValueError, NotImplementedError) as exc:
                logger.debug("classify_guard: solve failed: %s", exc)
                continue
            for sol in sols:
                if not (sol.is_real or sol.is_integer):
                    continue
                if sol.is_number:
                    n_star = int(sol) if sol.is_Integer else int(sp.ceiling(sol))
                    if n_star <= 0:
                        continue
                    before, at = _truth_at(n_star - 1), _truth_at(n_star)
                    if before is not None and at is not None and before != at:
                        return ("monotonic", n_star)
                    continue
                # Symbolic crossover (e.g. the incoming state at this
                # phase's start isn't a concrete literal): the direction
                # can't be verified purely symbolically here, so this is
                # reported provisionally -- callers that re-anchor on it
                # are expected to check the resulting state against the
                # target branch's guard before committing to it.
                return ("monotonic", sol)
    except (TypeError, ValueError) as exc:
        logger.debug("monotonic solve failed: %s", exc)

    # Periodicity probe: evaluate truth value for n = 0..P_max and look for
    # a repeating pattern.
    try:
        truths: list[bool] = []
        for i in range(p_max + 1):
            val = pred.subs(n, i)
            b = _sympy_as_bool(val)
            if b is None:
                # still symbolic – cannot decide
                return ("unknown", None)
            truths.append(b)
        # find least period
        for p in range(1, p_max // 2 + 1):
            if all(truths[i] == truths[i + p] for i in range(len(truths) - p)):
                # confirm it really repeats
                return ("periodic", p)
    except _SYMBOLIC_BESTEFFORT_EXC as exc:
        logger.debug("periodicity probe failed: %s", exc)

    return ("unknown", None)


# ---------------------------------------------------------------------------
# 5. stitch_phases
# ---------------------------------------------------------------------------

def _is_arith_sort(e: z3.ExprRef) -> bool:
    """Is *e* Int- or Real-sorted (i.e. safe to combine with +/-/*)?

    Bool/Array/String/BitVec/etc. variables can have a perfectly valid
    "closed form" (an untouched one is trivially constant across a
    phase), but they must never be combined arithmetically with anything
    -- Z3 raises a raw, uncatchable-by-callers sort-mismatch exception if
    you try.
    """
    try:
        return e.sort().kind() in (z3.Z3_INT_SORT, z3.Z3_REAL_SORT)
    except z3.Z3Exception:
        return False


def _sympy_to_z3(
    expr: sp.Expr, reverse_map: Mapping[sp.Symbol, z3.ExprRef]
) -> z3.ExprRef | None:
    """Best-effort inverse of :func:`_z3_to_sympy`.

    Turns a sympy expression built out of Add/Mul/Mod/Pow over symbols in
    *reverse_map* back into a Z3 arithmetic expression, so a boundary value
    computed symbolically (e.g. ``y0 + 5000 - x0``) can be carried into the
    next phase as a real Z3 expression instead of being discarded. Returns
    None if *expr* uses a symbol with no known Z3 counterpart, a symbol
    whose Z3 counterpart isn't Int/Real sorted (see :func:`_is_arith_sort`),
    or a construct this translator doesn't support (e.g. a symbolic
    exponent). Never raises: any Z3-level sort mismatch that slips through
    is caught and treated the same as "can't translate this".
    """
    if expr.is_Integer:
        return z3.IntVal(int(expr))
    if expr.is_Rational:
        return z3.RealVal(str(expr))
    if expr.is_Symbol:
        z3_expr = reverse_map.get(expr)
        if z3_expr is None or not _is_arith_sort(z3_expr):
            return None
        return z3_expr
    if isinstance(expr, sp.Add):
        parts = [_sympy_to_z3(a, reverse_map) for a in expr.args]
        if any(p is None for p in parts):
            return None
        try:
            out = parts[0]
            for p in parts[1:]:
                out = out + p
        except z3.Z3Exception as exc:
            logger.debug("_sympy_to_z3: Add failed: %s", exc)
            return None
        return out
    if isinstance(expr, sp.Mul):
        parts = [_sympy_to_z3(a, reverse_map) for a in expr.args]
        if any(p is None for p in parts):
            return None
        try:
            out = parts[0]
            for p in parts[1:]:
                out = out * p
        except z3.Z3Exception as exc:
            logger.debug("_sympy_to_z3: Mul failed: %s", exc)
            return None
        return out
    if isinstance(expr, sp.Mod):
        a = _sympy_to_z3(expr.args[0], reverse_map)
        m = _sympy_to_z3(expr.args[1], reverse_map)
        if a is None or m is None:
            return None
        try:
            return a % m
        except z3.Z3Exception as exc:
            logger.debug("_sympy_to_z3: Mod failed: %s", exc)
            return None
    if isinstance(expr, sp.Pow):
        base, exp = expr.args
        if isinstance(exp, sp.Integer) and exp >= 0:
            b = _sympy_to_z3(base, reverse_map)
            if b is None:
                return None
            try:
                out = z3.IntVal(1)
                for _ in range(int(exp)):
                    out = out * b
            except z3.Z3Exception as exc:
                logger.debug("_sympy_to_z3: Pow failed: %s", exc)
                return None
            return out
        return None
    return None


def _reanchor_value(
    cf: ClosedForm, n_star: int | sp.Expr, phase_i: int, fallback: z3.ExprRef
) -> z3.ExprRef:
    """Evaluate *cf* at ``n = n_star`` and turn it into a Z3 expression.

    Concrete numeric results become Z3 literals; results that still
    depend on free symbols are translated back into a real Z3 expression
    via ``cf.init_map`` (so e.g. ``y0 + 5000 - x0`` stays tied to the
    actual incoming state) rather than being replaced by a disconnected,
    unconstrained fresh variable. Falls back to *fallback* only when the
    substitution or translation genuinely can't be carried out.
    """
    n_sym = sp.Symbol("n", integer=True, nonnegative=True)
    try:
        val_sp = sp.simplify(cf.expr.subs(n_sym, n_star))
    except (TypeError, ValueError) as exc:
        logger.debug("PhaseFit: re-anchor subs failed for %s: %s", cf.var, exc)
        return fallback

    if not val_sp.free_symbols:
        if val_sp.is_Integer:
            return z3.IntVal(int(val_sp))
        if val_sp.is_Rational:
            return z3.RealVal(str(val_sp))
        return fallback

    z3_expr = _sympy_to_z3(val_sp, cf.init_map)
    return z3_expr if z3_expr is not None else fallback


def _branch_guard_consistent(
    branch: Branch, state: Mapping[z3.ExprRef, z3.ExprRef]
) -> bool | None:
    """Best-effort check: is *branch*'s guard satisfiable under *state*?

    Returns False only when the substituted guard is definitely UNSAT
    (i.e. the branch cannot possibly be the one active at this state),
    True when it's definitely SAT, and None when the check is
    inconclusive (still contains free symbols, or the solver can't decide
    quickly) -- in which case the caller should not treat it as a hard
    rejection.
    """
    try:
        substituted = z3.substitute(
            branch.guard, *[(k, v) for k, v in state.items()]
        )
        solver = z3.Solver()
        solver.set("timeout", 200)
        solver.add(substituted)
        result = solver.check()
    except z3.Z3Exception as exc:
        logger.debug("PhaseFit: branch consistency check failed: %s", exc)
        return None
    if result == z3.unsat:
        return False
    if result == z3.sat:
        return True
    return None


def stitch_phases(
    branches: Sequence[Branch],
    pre_vars: Sequence[z3.ExprRef],
    post_to_pre: Mapping[z3.ExprRef, z3.ExprRef],
    *,
    phase_budget: int = DEFAULT_PHASE_BUDGET_K,
    p_max: int = DEFAULT_P_MAX,
    initial_state: Mapping[z3.ExprRef, z3.ExprRef] | None = None,
    start_branch_idx: int = 0,
) -> tuple[list[Phase], list[PhaseBoundary]]:
    """Walk forward from n=0, alternating branches at discovered boundaries.

    Returns the list of phases and the list of boundaries found.
    Exceeding *phase_budget* aborts with the phases collected so far.

    Every closed form is computed in a *local* index (n=0 at the start of
    whatever phase is currently being solved, so re-anchoring is always a
    simple ``subs(n, n_local)``). ``Phase.start_n``/``Phase.end_n`` and
    ``PhaseBoundary.n_star``, however, are reported in the *global* index
    (steps since n=0 of phase 0), since that's what callers -- and
    assemble_candidates's interval-bound emission -- expect. The two are
    tracked separately and only combined when recording a boundary.

    *start_branch_idx* selects which branch is assumed active at n=0. The
    caller generally doesn't statically know which branch is active on
    entry (that's part of what's being discovered), so
    :func:`stitch_phases_from_all_starts` tries every branch as a starting
    point and lets downstream Houdini validation keep whichever guesses
    turn out to be consistent with the actual reachable states.
    """
    if not branches:
        return [], []

    phases: list[Phase] = []
    boundaries: list[PhaseBoundary] = []

    current_branch_idx = start_branch_idx % len(branches)
    current_init = dict(initial_state) if initial_state else {v: v for v in pre_vars}
    global_n: int | sp.Expr = 0  # global step count at the current phase's start

    for phase_i in range(phase_budget):
        branch = branches[current_branch_idx]
        cforms = compute_branch_closed_forms(
            branch, pre_vars, post_to_pre, current_init
        )
        if not cforms:
            # cannot obtain closed forms – stop
            break

        other_idxs = [i for i in range(len(branches)) if i != current_branch_idx]
        boundary_local_n: int | sp.Expr | None = None
        boundary_reason = ""
        next_idx = current_branch_idx

        # First try the current guard itself becoming false.
        kind, info = classify_guard(branch.guard, cforms, p_max=p_max)
        if kind == "monotonic":
            boundary_local_n = info
            boundary_reason = "monotonic"
            next_idx = other_idxs[0] if other_idxs else current_branch_idx
        elif kind == "periodic":
            # For periodic we create a phase of length = period and then
            # stay in the same "periodic regime" (simplified).
            boundary_local_n = info
            boundary_reason = "periodic"
            next_idx = current_branch_idx
        elif kind == "constant":
            # stays forever
            phases.append(Phase(
                index=phase_i,
                branch=branch,
                start_n=global_n,
                end_n=None,
                closed_forms=cforms,
                init_state=dict(current_init),
            ))
            break

        if boundary_local_n is None:
            # try classifying the other branches' guards
            for oi in other_idxs:
                kind2, info2 = classify_guard(branches[oi].guard, cforms, p_max=p_max)
                if kind2 == "monotonic":
                    boundary_local_n = info2
                    boundary_reason = "monotonic"
                    next_idx = oi
                    break

        if boundary_local_n is None:
            # No usable boundary found anywhere -- this phase runs forever.
            phases.append(Phase(
                index=phase_i,
                branch=branch,
                start_n=global_n,
                end_n=None,
                closed_forms=cforms,
                init_state=dict(current_init),
            ))
            break

        # Re-anchor: evaluate current closed forms at the (local) boundary
        # to obtain the initial state of the next phase.
        new_init: dict[z3.ExprRef, z3.ExprRef] = {
            v: _reanchor_value(cf, boundary_local_n, phase_i, current_init.get(v, v))
            for v, cf in cforms.items()
        }
        # Carry forward any pre_vars that didn't get a closed form (e.g. a
        # variable this branch doesn't touch at all) unchanged.
        for v in pre_vars:
            new_init.setdefault(v, current_init.get(v, v))

        # Sanity-check the chosen next branch against the re-anchored
        # state: if it's definitely inconsistent (e.g. re-entering a
        # branch whose own guard the new state already violates -- the
        # signature of picking the wrong side of a boundary), try the
        # other candidates before giving up on this phase's boundary.
        candidate_order = [next_idx, *[i for i in other_idxs if i != next_idx]]
        if boundary_reason == "periodic":
            candidate_order = [next_idx]  # periodic re-enters the same branch
        chosen_idx = None
        for cand in candidate_order:
            consistency = _branch_guard_consistent(branches[cand], new_init)
            if consistency is not False:
                chosen_idx = cand
                break
        if chosen_idx is None:
            # Every candidate branch is definitely inconsistent with the
            # re-anchored state -- the boundary we found isn't trustworthy.
            # Stop rather than commit to a nonsensical phase.
            phases.append(Phase(
                index=phase_i,
                branch=branch,
                start_n=global_n,
                end_n=None,
                closed_forms=cforms,
                init_state=dict(current_init),
            ))
            break
        next_idx = chosen_idx

        # int + int stays int; anything involving a sympy Expr promotes to
        # a sympy Expr -- either way this is the correct cumulative offset.
        global_end_n = global_n + boundary_local_n
        boundaries.append(PhaseBoundary(
            n_star=global_end_n,
            from_branch=current_branch_idx,
            to_branch=next_idx,
            reason=boundary_reason,
        ))
        phases.append(Phase(
            index=phase_i,
            branch=branch,
            start_n=global_n,
            end_n=global_end_n,
            closed_forms=cforms,
            init_state=dict(current_init),
        ))

        current_init = new_init
        current_branch_idx = next_idx
        global_n = global_end_n

    return phases, boundaries


# ---------------------------------------------------------------------------
# 6. assemble candidates
# ---------------------------------------------------------------------------

def assemble_candidates(
    phases: Sequence[Phase],
    relation_vars: Sequence[z3.ExprRef],
    extra_atoms: Sequence[z3.BoolRef] | None = None,
) -> list[z3.BoolRef]:
    """Build per-phase interval lemmas of the same shape phaserr uses.

    For each phase with concrete integer bounds [lo, hi) we emit, for every
    variable that has a closed form, inequalities that describe the possible
    values inside that interval (very conservative: just the bound atoms and
    the guard atoms themselves).

    Also includes any extra atoms (e.g. raw guard atoms from SeedMiner).
    """
    cands: list[z3.BoolRef] = []
    if extra_atoms:
        cands.extend(extra_atoms)

    for ph in phases:
        lo = ph.start_n
        hi = ph.end_n
        # Emit the phase-guard atoms projected onto the relation variables
        # (they are already over pre-state).
        try:
            # Simple: the branch guard itself is a useful candidate
            if not z3.is_true(ph.branch.guard):
                cands.append(ph.branch.guard)
        except z3.Z3Exception as exc:
            logger.debug("assemble_candidates: guard atom skipped: %s", exc)

        n_sym = sp.Symbol("n", integer=True, nonnegative=True)

        # For concrete numeric bounds emit n-related inequalities when a
        # variable is known to be equal to the index (identity recurrence).
        for v, cf in ph.closed_forms.items():
            # If the closed form is simply “n” or “n + c”, emit bounds
            try:
                if cf.expr == n_sym or (cf.expr - n_sym).is_constant():
                    # v is essentially the loop counter
                    if isinstance(lo, int):
                        cands.append(v >= z3.IntVal(lo))
                    if isinstance(hi, int):
                        cands.append(v < z3.IntVal(hi))
            except (TypeError, ValueError) as exc:
                logger.debug("assemble_candidates: bound skipped for %s: %s", v, exc)

            # Constant closed form inside the phase → equality candidate.
            # Note: use `is_Integer` (is this expression *literally* a
            # concrete integer) rather than the `is_integer` *assumption*
            # query, which is also true for e.g. a bare Symbol declared
            # `integer=True` -- such a symbol has no free `n` but is not a
            # number, and `int()` on it raises.
            if n_sym not in cf.expr.free_symbols and cf.expr.is_Integer:
                cands.append(v == z3.IntVal(int(cf.expr)))

        # Two variables that grow at the same rate (same coefficient of n,
        # i.e. their closed forms differ by an n-independent amount) stay
        # at a fixed offset from each other for the whole phase. This is
        # exactly what proves e.g. "y == x" once two variables that used to
        # move independently start incrementing together (the headline
        # PhaseFit example). Detect it by diffing the two closed forms
        # symbolically, then resolving the (n-independent) remainder back
        # to a real Z3 value via each variable's own init_map so it's
        # checked against the actual re-anchored state, not just the
        # placeholder symbol names.
        items = list(ph.closed_forms.items())
        for i, (v1, cf1) in enumerate(items):
            if not _is_arith_sort(v1):
                continue
            for v2, cf2 in items[i + 1:]:
                # Both sides of `v1 == v2 (+ c)` must be the same,
                # arithmetic sort -- comparing e.g. an Int var against a
                # Bool/Array/String one (or adding a literal to one) is a
                # Z3 sort error, not something to even attempt here.
                if v1.sort() != v2.sort() or not _is_arith_sort(v2):
                    continue
                try:
                    diff = sp.simplify(cf1.expr - cf2.expr)
                except (TypeError, ValueError) as exc:
                    logger.debug("assemble_candidates: diff failed: %s", exc)
                    continue
                if n_sym in diff.free_symbols:
                    continue  # different growth rate within this phase
                merged_map = {**cf2.init_map, **cf1.init_map}
                z3_diff = _sympy_to_z3(diff, merged_map)
                if z3_diff is None:
                    continue
                try:
                    simplified = z3.simplify(z3_diff)
                except z3.Z3Exception as exc:
                    logger.debug("assemble_candidates: simplify failed: %s", exc)
                    continue
                if z3.is_int_value(simplified):
                    const = simplified.as_long()
                    cands.append(
                        v1 == v2 if const == 0 else v1 == v2 + z3.IntVal(const)
                    )


    # Deduplicate by sexpr string
    seen: set[str] = set()
    unique: list[z3.BoolRef] = []
    for c in cands:
        s = c.sexpr()
        if s not in seen:
            seen.add(s)
            unique.append(c)
    return unique


def _drop_foreign_variable_candidates(
    cands: Sequence[z3.BoolRef], allowed: Sequence[z3.ExprRef]
) -> list[z3.BoolRef]:
    """Drop any candidate that references a variable outside *allowed*.

    PhaseFit's guard/closed-form candidates are built from whatever
    variables happen to appear in the rule body -- including rule-local
    existentials that are never assigned anywhere (a common "havoc"
    pattern, e.g. ``(= 0 val1)`` where ``val1`` is a free nondeterministic
    input, not a relation argument). The pre_var → canonical-var
    projection in ``_analyse_rule`` only rewrites *known* pre_vars; it has
    nothing to substitute a genuinely foreign variable with, so one could
    otherwise reach MultiHoudini and fail its own (correct, defensive)
    validation with a raw, uncaught ``ValueError`` instead of PhaseFit
    just quietly not proposing that particular candidate.
    """
    allowed_ids = {v.get_id() for v in allowed}
    kept: list[z3.BoolRef] = []
    for c in cands:
        try:
            free = get_vars(c)
        except z3.Z3Exception as exc:
            logger.debug("PhaseFit: get_vars failed for candidate %s: %s", c, exc)
            continue
        if all(v.get_id() in allowed_ids for v in free):
            kept.append(c)
        else:
            logger.debug(
                "PhaseFit: dropping candidate with foreign variable(s): %s", c
            )
    return kept


def stitch_phases_from_all_starts(
    branches: Sequence[Branch],
    pre_vars: Sequence[z3.ExprRef],
    post_to_pre: Mapping[z3.ExprRef, z3.ExprRef],
    *,
    phase_budget: int = DEFAULT_PHASE_BUDGET_K,
    p_max: int = DEFAULT_P_MAX,
    initial_state: Mapping[z3.ExprRef, z3.ExprRef] | None = None,
) -> tuple[list[Phase], list[PhaseBoundary]]:
    """Try every branch as the phase-0 starting point and merge the results.

    PhaseFit generally has no static way of knowing which branch's guard
    is actually satisfied by the states that reach this rule on entry --
    that's part of what the surrounding fixed-point computation is trying
    to discover. Rather than hardcoding a single (frequently wrong)
    starting branch, this explores each one and lets downstream Houdini
    validation keep whichever resulting candidates actually hold; wrong
    guesses just fail validation and get dropped, per the guess-then-
    validate design (see docs/phasefit-branching-loop-solver-design.md).
    """
    all_phases: list[Phase] = []
    all_boundaries: list[PhaseBoundary] = []
    for start in range(len(branches)):
        phases, boundaries = stitch_phases(
            branches,
            pre_vars,
            post_to_pre,
            phase_budget=phase_budget,
            p_max=p_max,
            initial_state=initial_state,
            start_branch_idx=start,
        )
        all_phases.extend(phases)
        all_boundaries.extend(boundaries)
    return all_phases, all_boundaries


# ---------------------------------------------------------------------------
# Top-level driver
# ---------------------------------------------------------------------------

@dataclass
class PhaseFit:
    """Run the PhaseFit synthesis pipeline on a HornProgram."""

    program: HornProgram
    phase_budget: int = DEFAULT_PHASE_BUDGET_K
    p_max: int = DEFAULT_P_MAX
    per_variable_branches: bool = True

    def run(
        self,
        *,
        seed_result: SeedMiningResult | None = None,
    ) -> list[PhaseFitResult]:
        """Analyse every inductive rule and return PhaseFitResult objects.

        Candidates from all results can be merged into a CandidateMap and
        handed to MultiHoudini.
        """
        if seed_result is None:
            miner = SeedMiner(self.program)
            seed_result = miner.mine()

        results: list[PhaseFitResult] = []
        for rule in self.program.rules:
            if not rule.is_inductive:
                continue
            res = self._analyse_rule(rule, seed_result)
            results.append(res)
        return results

    def _analyse_rule(
        self,
        rule: HornRule,
        seed_result: SeedMiningResult,
    ) -> PhaseFitResult:
        rel = rule.src_relation
        if rel is None:
            # is_inductive already guarantees src_relation is not None for
            # any rule reaching here, but guard against it defensively
            # instead of asserting: assertions can be stripped (python -O)
            # and this module never uses bare asserts for control flow.
            return PhaseFitResult(
                relation=rule.dst_relation,
                phases=[],
                boundaries=[],
                candidates=[],
                success=False,
                message="rule has no source relation (not inductive)",
            )
        pre_vars = rule.src_args
        # Map post → pre by position (same arity)
        post_to_pre = {
            post: pre
            for post, pre in zip(rule.dst_args, rule.src_args)
        }

        branches = extract_guarded_branches(
            rule, per_variable=self.per_variable_branches
        )
        if not branches:
            return PhaseFitResult(
                relation=rel,
                phases=[],
                boundaries=[],
                candidates=[],
                success=False,
                message="no guarded branches extracted",
            )

        # Seed atoms already mined for this relation
        extra = list(seed_result.candidates.get(rel, ()))

        phases, boundaries = stitch_phases_from_all_starts(
            branches,
            pre_vars,
            post_to_pre,
            phase_budget=self.phase_budget,
            p_max=self.p_max,
        )
        raw_cands = assemble_candidates(phases, pre_vars, extra_atoms=extra)

        # Project rule-local variables onto the SeedMiner canonical variables
        # so MultiHoudini accepts the candidates.
        canonical = seed_result.variables.get(rel)
        if canonical is not None and len(canonical) == len(pre_vars):
            from .seedminer import _direct_argument_substitutions
            subs = _direct_argument_substitutions(tuple(pre_vars), canonical)
            if subs:
                projected: list[z3.BoolRef] = []
                for c in raw_cands:
                    try:
                        projected.append(z3.substitute(c, *subs))
                    except z3.Z3Exception:
                        projected.append(c)
                cands = projected
            else:
                cands = raw_cands
        else:
            cands = raw_cands

        # Final safety net: projection above only rewrites *known*
        # pre_vars -- it can't do anything about a genuinely foreign
        # variable (e.g. a rule-local havoc/existential that was never
        # assigned anywhere but appears inside a guard). Drop any
        # candidate that still isn't expressed purely over the relation's
        # own arguments, rather than letting it reach MultiHoudini's
        # stricter validation and crash the whole run.
        cands = _drop_foreign_variable_candidates(
            cands, canonical if canonical is not None else pre_vars
        )

        return PhaseFitResult(
            relation=rel,
            phases=phases,
            boundaries=boundaries,
            candidates=cands,
            success=bool(phases),
            message=f"{len(phases)} phase(s), {len(boundaries)} boundary(ies)",
        )

    def candidates_as_map(
        self,
        results: Sequence[PhaseFitResult],
    ) -> CandidateMap:
        """Merge all PhaseFit candidates into a CandidateMap suitable for
        MultiHoudini.run."""
        out: dict[z3.FuncDeclRef, list[z3.BoolRef]] = {}
        for res in results:
            out.setdefault(res.relation, []).extend(res.candidates)
        # freeze
        return {rel: tuple(cands) for rel, cands in out.items()}


def run_phasefit(
    program: HornProgram,
    *,
    phase_budget: int = DEFAULT_PHASE_BUDGET_K,
    p_max: int = DEFAULT_P_MAX,
    seed_result: SeedMiningResult | None = None,
) -> tuple[list[PhaseFitResult], CandidateMap]:
    """Convenience entry point.

    Returns the per-rule results and the merged candidate map.
    """
    pf = PhaseFit(program, phase_budget=phase_budget, p_max=p_max)
    results = pf.run(seed_result=seed_result)
    cmap = pf.candidates_as_map(results)
    return results, cmap
