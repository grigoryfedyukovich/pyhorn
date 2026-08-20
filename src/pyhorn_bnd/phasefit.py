"""PhaseFit: weaker closed-form synthesis for branching (ite/mod) loops.

Implements the design in docs/phasefit-branching-loop-solver-design.md.

Positioning: a second, lower-power synthesis strategy that targets loops whose
per-step updates contain ``ite``/``mod`` (FreqHorn's ``s_split_*`` family).
Uses a guess-then-validate approach: every candidate still passes through
MultiHoudini / checkFact / checkConsecution / checkQuery before acceptance.

Pipeline overview
-----------------
1. extract_mbp_guarded_branches – enumerate phase guards with model-based projection
   (with the existing ite flattener as a fallback)
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
    """A simultaneous pure update for several variables under a common guard.

    ``witness_model`` and ``guard_source`` make the control-flow provenance
    explicit for MBP-derived phases: the guard and update arm are selected
    from the same transition model, and downstream Phase/lemma construction
    keeps them together.
    """

    guard: z3.BoolRef
    updates: dict[z3.ExprRef, z3.ExprRef]  # post_var -> pure expr in pre vars
    # Optional name for debugging
    label: str = ""
    # Representative transition model used to select the update arm.
    witness_model: z3.ModelRef | None = None
    # Provenance for the guard; e.g. "mbp" or "ite-flatten".
    guard_source: str = ""


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
# 2b. MBP-based phase guards (ImplCheck-style)
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class MBPPhase:
    """One model-guided projection of a transition onto source variables."""

    guard: z3.BoolRef
    model: z3.ModelRef


def _transition_formula(rule: HornRule) -> z3.BoolRef | None:
    """Return the rule-local transition constraint, excluding CHC relations.

    For an inductive rule, ``rule.body`` contains the source relation atom plus
    transition constraints (and occasionally auxiliary relation-free atoms).
    MBP should project the latter, not quantify over the source predicate.
    """
    if not rule.is_inductive:
        return None
    conjuncts = list(rule.body.children()) if z3.is_and(rule.body) else [rule.body]
    tr: list[z3.BoolRef] = []
    for c in conjuncts:
        if z3.is_app(c) and c.decl() in {
            rule.src_relation,
            rule.dst_relation,
        }:
            continue
        tr.append(c)
    return z3.And(*tr) if tr else z3.BoolVal(True)


def _expand_term_ites_in_formula(formula: z3.BoolRef) -> z3.BoolRef:
    """Expand term-level ITEs into Boolean branching before MBP literal selection.

    The ImplCheck MBP algorithm operates on Boolean literals in NNF.  CHC
    frontends commonly encode control flow as term-level ``ite`` inside SSA
    equalities, so we expose those alternatives logically here.  This is only
    a local Boolean expansion; MBP still avoids eagerly converting the whole
    transition relation to a global DNF.
    """
    if z3.is_and(formula):
        return z3.And(*[_expand_term_ites_in_formula(c) for c in formula.children()])
    if z3.is_or(formula):
        return z3.Or(*[_expand_term_ites_in_formula(c) for c in formula.children()])
    if z3.is_not(formula):
        return z3.Not(_expand_term_ites_in_formula(formula.arg(0)))
    if not z3.is_app(formula) or formula.num_args() == 0:
        return formula

    # Look for a top-level term ITE in any argument.  Split only on the first
    # one and recurse, preserving sharing/order through nested conditionals.
    for i, child in enumerate(formula.children()):
        if _is_ite(child):
            cond, then_t, else_t = child.arg(0), child.arg(1), child.arg(2)
            then_args = list(formula.children())
            else_args = list(formula.children())
            then_args[i] = then_t
            else_args[i] = else_t
            then_atom = formula.decl()(*then_args)
            else_atom = formula.decl()(*else_args)
            return z3.Or(
                z3.And(cond, _expand_term_ites_in_formula(then_atom)),
                z3.And(z3.Not(cond), _expand_term_ites_in_formula(else_atom)),
            )

    rebuilt = formula
    try:
        kids = [_expand_term_ites_in_formula(c) if z3.is_bool(c) else c
                for c in formula.children()]
        if any(not a.eq(b) for a, b in zip(kids, formula.children())):
            rebuilt = formula.decl()(*kids)
    except z3.Z3Exception:
        pass
    return rebuilt


def _nnf_formula(formula: z3.BoolRef) -> z3.BoolRef | None:
    """Normalize *formula* to NNF using Z3's tactic when available."""
    try:
        goal = z3.Goal()
        goal.add(_expand_term_ites_in_formula(formula))
        result = z3.Tactic("nnf")(goal)
        if len(result) != 1:
            return z3.Or(*[g.as_expr() for g in result])
        return z3.simplify(result[0].as_expr())
    except z3.Z3Exception as exc:
        logger.debug("PhaseFit MBP: NNF conversion failed: %s", exc)
        return None


def _nnf_literals(formula: z3.BoolRef) -> list[z3.BoolRef]:
    """Collect literal leaves from a formula already in NNF."""
    if z3.is_and(formula) or z3.is_or(formula):
        out: list[z3.BoolRef] = []
        for child in formula.children():
            out.extend(_nnf_literals(child))
        return out
    return [formula]


def _model_satisfies(model: z3.ModelRef, formula: z3.BoolRef) -> bool:
    try:
        return z3.is_true(model.eval(formula, model_completion=True))
    except z3.Z3Exception:
        return False


def _qe_exists(vars_to_eliminate: Sequence[z3.ExprRef], body: z3.BoolRef) -> z3.BoolRef | None:
    """Eliminate *vars_to_eliminate* using Z3's QE tactic."""
    if not vars_to_eliminate:
        return z3.simplify(body)
    try:
        q = z3.Exists(list(vars_to_eliminate), body)
        goal = z3.Goal()
        goal.add(q)
        result = z3.Tactic("qe")(goal)
        if len(result) == 0:
            return z3.BoolVal(False)
        exprs = [z3.simplify(g.as_expr()) for g in result]
        out = exprs[0]
        for e in exprs[1:]:
            out = z3.Or(out, e)
        return z3.simplify(out)
    except z3.Z3Exception as exc:
        logger.debug("PhaseFit MBP: QE failed: %s", exc)
        return None


def _mbp_direct_project(
    true_literals: Sequence[z3.BoolRef],
    post_vars: Sequence[z3.ExprRef],
) -> tuple[z3.BoolRef, bool] | None:
    """Fast MBP projection for SSA-style transitions.

    Most FreqHorn transitions define every post variable with an equality such
    as ``x' = t(pre)``.  In that case existential elimination is just
    substitution; invoking Z3's general-purpose QE here is both unnecessary
    and, for nested ITEs, extremely expensive.  Returns ``(guard, True)`` when
    every post variable can be eliminated this way.
    """
    post_ids = {v.get_id(): v for v in post_vars}
    defs: dict[int, z3.ExprRef] = {}

    for lit in true_literals:
        if not z3.is_eq(lit):
            continue
        lhs, rhs = lit.arg(0), lit.arg(1)
        for post, term in ((lhs, rhs), (rhs, lhs)):
            if not z3.is_const(post) or post.get_id() not in post_ids:
                continue
            # Only orient an equality when the opposite side contains no
            # post-state variables.  This keeps the projection acyclic and
            # avoids guessing about relational post-state constraints.
            if any(v.get_id() in post_ids for v in get_vars(term)):
                continue
            defs[post.get_id()] = term
            break

    if not defs or any(v.get_id() not in defs for v in post_vars):
        return None

    body = z3.And(*true_literals)
    # Repeatedly substitute in case a definition refers to another defined
    # post variable (the usual SSA chain).
    for _ in range(len(defs) + 1):
        changed = False
        for pid, rhs in defs.items():
            post = post_ids[pid]
            new_body = z3.substitute(body, (post, rhs))
            if not new_body.eq(body):
                body = new_body
                changed = True
        if not changed:
            break

    if any(v.get_id() in post_ids for v in get_vars(body)):
        return None
    return z3.simplify(body), True


def _mbp_phase_guard_with_mode(
    model: z3.ModelRef,
    transition: z3.BoolRef,
    post_vars: Sequence[z3.ExprRef],
) -> tuple[z3.BoolRef | None, bool]:
    """Return an MBP guard and whether it was projected without general QE."""
    nnf = _nnf_formula(transition)
    if nnf is None:
        return None, False
    true_literals = [
        lit for lit in _nnf_literals(nnf)
        if _model_satisfies(model, lit)
    ]
    if not true_literals:
        return None, False

    direct = _mbp_direct_project(true_literals, post_vars)
    if direct is not None:
        return direct
    return _qe_exists(post_vars, z3.And(*true_literals)), False


def mbp_phase_guard(
    model: z3.ModelRef,
    transition: z3.BoolRef,
    post_vars: Sequence[z3.ExprRef],
) -> z3.BoolRef | None:
    """Construct one LIA MBP, following ImplCheck Algorithm 1.

    The fast path performs exact existential elimination by SSA substitution;
    general QE is retained as a fallback for non-SSA transitions.
    """
    guard, _ = _mbp_phase_guard_with_mode(model, transition, post_vars)
    return guard


def all_mbp_phase_guards(
    transition: z3.BoolRef,
    pre_vars: Sequence[z3.ExprRef],
    post_vars: Sequence[z3.ExprRef],
    *,
    max_guards: int = 32,
    timeout_ms: int = 500,
) -> list[MBPPhase]:
    """Lazily enumerate MBPs until the transition is covered.

    This is ImplCheck's Algorithm 3: repeatedly obtain a model of the
    transition not covered by the previously generated source-state guards,
    construct its MBP, and continue until no uncovered transition remains.
    """
    guards: list[MBPPhase] = []
    projected_transition: z3.BoolRef | None = None
    for _ in range(max_guards):
        solver = z3.Solver()
        solver.set("timeout", timeout_ms)
        solver.add(transition)
        if guards:
            solver.add(z3.Not(z3.Or(*[g.guard for g in guards])))
        result = solver.check()
        if result != z3.sat:
            break
        model = solver.model()
        guard, exact_projection = _mbp_phase_guard_with_mode(
            model, transition, post_vars
        )
        if guard is None or z3.is_false(guard):
            # Projection failed (or was vacuous) for *this* model/cube.
            # z3.Solver().check() is not guaranteed to return the same
            # model on the next iteration for the same constraints, and a
            # different not-yet-covered model may project just fine, so
            # keep searching rather than abandoning the whole enumeration
            # -- bounded by max_guards either way. See
            # test_all_mbp_phase_guards_recovers_after_a_bad_model.
            continue
        # The SSA fast path is an exact projection of the model-selected
        # literals, so no global QE is needed.  For non-SSA transitions, retain
        # the old soundness check, but cache the expensive projection once.
        if not exact_projection:
            if projected_transition is None:
                projected_transition = _qe_exists(post_vars, transition)
            if projected_transition is None:
                break
            sound_solver = z3.Solver()
            sound_solver.set("timeout", timeout_ms)
            sound_solver.add(guard, z3.Not(projected_transition))
            if sound_solver.check() != z3.unsat:
                # This specific model's cube produced an unsound (over-
                # approximating) guard -- discard just this one and keep
                # looking. Bailing out entirely here would abandon
                # coverage of every other, still-uncovered transition
                # over one bad cube.
                continue
        if any(z3.simplify(guard).eq(z3.simplify(old.guard)) for old in guards):
            break
        guards.append(MBPPhase(guard=guard, model=model))
    return guards


def _projection_is_sound(
    guard: z3.BoolRef,
    transition: z3.BoolRef,
    post_vars: Sequence[z3.ExprRef],
    timeout_ms: int,
) -> bool:
    """Check guard => exists post-state.  This is the MBP soundness condition."""
    projected = _qe_exists(post_vars, transition)
    if projected is None:
        return False
    solver = z3.Solver()
    solver.set("timeout", timeout_ms)
    solver.add(guard, z3.Not(projected))
    return solver.check() == z3.unsat


def _select_ite_under_model(expr: z3.ExprRef, model: z3.ModelRef) -> z3.ExprRef:
    """Replace term-level ITEs by the arm selected by *model*."""
    if _is_ite(expr):
        cond = expr.arg(0)
        chosen = expr.arg(1) if _model_satisfies(model, cond) else expr.arg(2)
        return _select_ite_under_model(chosen, model)
    if not z3.is_app(expr) or expr.num_args() == 0:
        return expr
    kids = [_select_ite_under_model(c, model) for c in expr.children()]
    if all(a.eq(b) for a, b in zip(kids, expr.children())):
        return expr
    try:
        return expr.decl()(*kids)
    except z3.Z3Exception:
        return expr


def extract_mbp_guarded_branches(rule: HornRule) -> list[Branch]:
    """Extract phase branches using MBP guards rather than source-code guards.

    The model returned for each MBP identifies the concrete control-flow arm
    of term-level ``ite`` updates.  The phase guard itself comes only from MBP,
    so the method also works when the useful phase condition is not exposed as
    a predicate that SeedMiner can extract syntactically.
    """
    transition = _transition_formula(rule)
    if transition is None:
        return []
    mbps = all_mbp_phase_guards(
        transition,
        rule.src_args,
        rule.dst_args,
    )
    # print(f"PhaseFit MBPs for {rule}: {len(mbps)}")
    # for i, mbp in enumerate(mbps):
    #     print(f"  MBP {i}: guard = {mbp.guard}")
    #     print(f"       model = {mbp.model}")
    if not mbps:
        return []

    # Recover equalities for ordinary SSA-style updates.  For each destination
    # variable, choose the term from the active ITE arm under the representative
    # model.  This lets MBP supply the guard without throwing away the existing
    # closed-form machinery.
    defs: dict[int, z3.ExprRef] = {}
    for lhs, rhs in _collect_equalities(transition):
        defs[lhs.get_id()] = rhs

    branches: list[Branch] = []
    src_ids = {v.get_id() for v in rule.src_args}
    for i, mbp in enumerate(mbps):
        updates: dict[z3.ExprRef, z3.ExprRef] = {}
        for idx, post in enumerate(rule.dst_args):
            rhs = defs.get(post.get_id())
            if rhs is None:
                try:
                    rhs = rule.src_args[idx]
                except IndexError:
                    rhs = post
            updates[post] = _fully_expand(
                _select_ite_under_model(rhs, mbp.model),
                defs,
                src_ids,
            )

        branch = Branch(
            guard=mbp.guard,
            updates=updates,
            label=f"mbp-{i}",
            witness_model=mbp.model,
            guard_source="mbp",
        )

        # The MBP guard and the selected update arm must describe the same
        # phase.  Since MBP projects a model-selected conjunction, verify
        # that the selected pure updates satisfy the original transition
        # throughout the entire projected guard, not merely at the witness
        # model.  Otherwise we would be pairing a valid guard with an update
        # arm that is only locally correct.
        if not _branch_update_matches_guard(branch.guard, branch.updates, transition, rule.dst_args):
            logger.debug(
                "PhaseFit MBP: rejecting phase %s because guard/update "
                "alignment could not be certified",
                branch.label,
            )
            continue

        branches.append(branch)
    return branches


def _branch_update_matches_guard(
    guard: z3.BoolRef,
    updates: Mapping[z3.ExprRef, z3.ExprRef],
    transition: z3.BoolRef,
    post_vars: Sequence[z3.ExprRef],
) -> bool:
    """Check that an MBP guard selects the supplied update branch globally.

    This is the key provenance invariant for PhaseFit phases: the branch
    guard must imply that its associated concrete update satisfies the
    original transition relation.  The check is intentionally independent
    of the witness model.
    """
    try:
        instantiated = z3.substitute(
            transition,
            *[(post, updates[post]) for post in post_vars if post in updates],
        )
    except z3.Z3Exception:
        return False
    solver = z3.Solver()
    solver.set("timeout", 500)
    solver.add(guard, z3.Not(instantiated))
    return solver.check() == z3.unsat


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

        # Concretize symbolic boundaries using known integer inits (from facts
        # or a previous re-anchor).  E.g. n* = 5000 - x0_0 with x0_0=0 → 5000.
        if not isinstance(boundary_local_n, int) and isinstance(boundary_local_n, sp.Expr):
            # Build a temporary init_map from all closed forms
            merged_imap: dict = {}
            for cf in cforms.values():
                merged_imap.update(cf.init_map)
            conc = _concretize_sympy(boundary_local_n, current_init, merged_imap)
            gi = _ground_int(conc)
            if gi is not None and gi >= 0:
                boundary_local_n = gi

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

def _concretize_sympy(
    expr: sp.Expr,
    init_state: Mapping[z3.ExprRef, z3.ExprRef] | None,
    init_map: Mapping[sp.Symbol, z3.ExprRef] | None = None,
) -> sp.Expr:
    """Substitute known concrete integer inits into a sympy closed form / boundary."""
    if not init_state and not init_map:
        return expr
    subs: dict[sp.Symbol, sp.Integer] = {}
    # init_map: sympy symbol -> Z3 expression (often a pre-var or IntVal)
    if init_map:
        for sym, zexpr in init_map.items():
            if z3.is_int_value(zexpr):
                subs[sym] = sp.Integer(zexpr.as_long())
            elif init_state is not None:
                # zexpr may be a pre-var; look up its concrete value in init_state
                for pv, val in init_state.items():
                    if pv.get_id() == getattr(zexpr, "get_id", lambda: None)():
                        if z3.is_int_value(val):
                            subs[sym] = sp.Integer(val.as_long())
                        break
    # Also: if expr still has free symbols matching the exact sympy name
    # compute_closed_form uses for a var's init symbol (f"{var}_0"), bind
    # those too. This must be an EXACT name match, not a loose heuristic:
    # every init symbol produced by compute_closed_form ends in "_0" (that
    # suffix alone matches everything, not just this specific variable),
    # and a Z3 variable's numeric get_id() is not otherwise embedded in
    # its printed name, so neither is a safe way to identify "the init
    # symbol for *this* pv" among several. Getting this wrong silently
    # binds one variable's init symbol to a *different* variable's
    # concrete value -- confirmed via
    # test_concretize_sympy_does_not_cross_bind_variables.
    if init_state:
        for pv, val in init_state.items():
            if not z3.is_int_value(val):
                continue
            expected = sp.Symbol(f"{pv}_0", integer=True)
            if expected in expr.free_symbols and expected not in subs:
                subs[expected] = sp.Integer(val.as_long())
    if not subs:
        return expr
    try:
        return sp.simplify(expr.subs(subs))
    except _SYMBOLIC_BESTEFFORT_EXC:
        return expr


def _ground_int(expr: sp.Expr) -> int | None:
    try:
        if expr.is_Integer:
            return int(expr)
    except (AttributeError, TypeError, ValueError):
        pass
    return None


def assemble_candidates(
    phases: Sequence[Phase],
    relation_vars: Sequence[z3.ExprRef],
    extra_atoms: Sequence[z3.BoolRef] | None = None,
    *,
    global_init: Mapping[z3.ExprRef, z3.ExprRef] | None = None,
) -> list[z3.BoolRef]:
    """Build phase-local lemmas from closed forms, guarded by the phase guard.

    Improvements over the minimal emitter:
    * Concrete fact-init values are substituted into closed forms so constant
      phases yield real equalities (e.g. ``y == 5000`` under ``x < 5000``).
    * Affine closed forms ``v(n) = a*n + b`` with ground ``a,b`` and concrete
      phase bounds produce interval lemmas on ``v``.
    * When one variable tracks the step counter and another is constant on the
      phase, emit the constant and the counter bounds implied by the guard.
    * Raw phase-guard comparison atoms (over relation vars only) are also
      proposed -- they help close off-by-one gaps at boundaries (design §6).
    * Cross-variable n-independent offsets become guarded equalities when the
      offset is ground after init substitution.
    """
    cands: list[z3.BoolRef] = []
    if extra_atoms:
        cands.extend(extra_atoms)

    rel_ids = {v.get_id() for v in relation_vars}
    n_sym = sp.Symbol("n", integer=True, nonnegative=True)

    for ph in phases:
        guard = ph.branch.guard
        # Prefer phase-local init (re-anchored); fall back to global fact init.
        # Copy rather than alias ph.init_state -- setdefault below must not
        # mutate the Phase object itself (confirmed: aliasing here silently
        # leaked global_init entries into ph.init_state as a side effect).
        phase_init = dict(ph.init_state) if ph.init_state else {}
        if global_init:
            for k, v in global_init.items():
                phase_init.setdefault(k, v)

        def emit(lemma: z3.BoolRef) -> None:
            try:
                if z3.is_true(guard):
                    cands.append(lemma)
                else:
                    cands.append(z3.Implies(guard, lemma))
            except z3.Z3Exception as exc:
                logger.debug("assemble_candidates: guarded lemma skipped: %s", exc)

        # --- (a) phase-guard atoms as candidates (design §6) ---------------
        def _emit_guard_atoms(g: z3.BoolRef) -> None:
            if z3.is_true(g) or z3.is_false(g):
                return
            if z3.is_and(g):
                for c in g.children():
                    _emit_guard_atoms(c)
                return
            # Anything else (a comparison atom, an Or, or a Not(atom)) is
            # kept as one unit candidate when all its free vars are local
            # to the relation.
            try:
                free = get_vars(g)
            except z3.Z3Exception:
                return
            if free and all(v.get_id() in rel_ids for v in free):
                cands.append(g)

        _emit_guard_atoms(guard)

        lo = ph.start_n
        hi = ph.end_n
        # Concretize symbolic phase bounds using known inits
        if not isinstance(lo, int) and isinstance(lo, sp.Expr):
            lo_c = _concretize_sympy(lo, phase_init)
            gi = _ground_int(lo_c)
            if gi is not None:
                lo = gi
        if not isinstance(hi, int) and isinstance(hi, sp.Expr):
            hi_c = _concretize_sympy(hi, phase_init)
            gi = _ground_int(hi_c)
            if gi is not None:
                hi = gi

        for v, cf in ph.closed_forms.items():
            if not _is_arith_sort(v):
                continue
            # Substitute concrete inits into the closed form
            expr = _concretize_sympy(cf.expr, phase_init, cf.init_map)

            # (b) fully ground constant closed form
            gi = _ground_int(expr) if n_sym not in expr.free_symbols else None
            if gi is not None:
                emit(v == z3.IntVal(gi))
                continue

            # (c) constant w.r.t. n but still symbolic -- if it reduces to a
            # single init variable that we know is this var's own pre-value,
            # skip (tautology). If it reduces to another var, emit equality.
            if n_sym not in expr.free_symbols:
                z3e = _sympy_to_z3(expr, cf.init_map)
                if z3e is not None:
                    try:
                        z3e = z3.simplify(z3e)
                        if phase_init:
                            z3e = z3.simplify(
                                z3.substitute(z3e, *[(k, val) for k, val in phase_init.items()])
                            )
                        if z3.is_int_value(z3e):
                            emit(v == z3e)
                        elif z3.is_const(z3e) and z3e.get_id() != v.get_id():
                            # v equals some other relation var throughout the phase
                            if z3e.get_id() in rel_ids:
                                emit(v == z3e)
                    except z3.Z3Exception as exc:
                        logger.debug("assemble: const CF z3 failed: %s", exc)

            # (d) counter-like: expr = n + c  (c ground after init subst)
            try:
                shifted = sp.simplify(expr - n_sym)
                if n_sym not in shifted.free_symbols:
                    c_val = _ground_int(shifted)
                    if c_val is not None:
                        # v == n + c  ⇒  under concrete [lo, hi) bounds on v
                        if isinstance(lo, int):
                            emit(v >= z3.IntVal(lo + c_val))
                        if isinstance(hi, int):
                            emit(v < z3.IntVal(hi + c_val))
                        # Also: if guard is a threshold on v, the dual var
                        # bounds are already covered by guard atoms.
            except _SYMBOLIC_BESTEFFORT_EXC as exc:
                logger.debug("assemble: counter form failed for %s: %s", v, exc)

            # (e) general affine: a*n + b with ground a,b and concrete bounds
            try:
                poly = sp.Poly(sp.expand(expr), n_sym)
                if poly.degree() == 1:
                    a = poly.coeff_monomial(n_sym)
                    b = poly.coeff_monomial(1)
                    if a.is_Integer and (b.is_Integer or n_sym not in b.free_symbols):
                        ai = int(a)
                        bi = _ground_int(b)
                        if bi is not None and isinstance(lo, int) and isinstance(hi, int):
                            # range of a*n+b over n in [lo, hi)
                            ends = [ai * lo + bi, ai * (hi - 1) + bi]
                            emit(v >= z3.IntVal(min(ends)))
                            emit(v <= z3.IntVal(max(ends)))
            except _SYMBOLIC_BESTEFFORT_EXC:
                pass

        # (f) cross-variable n-independent offsets (ground after init subst)
        items = list(ph.closed_forms.items())
        for i, (v1, cf1) in enumerate(items):
            if not _is_arith_sort(v1):
                continue
            for v2, cf2 in items[i + 1:]:
                if v1.sort() != v2.sort() or not _is_arith_sort(v2):
                    continue
                try:
                    e1 = _concretize_sympy(cf1.expr, phase_init, cf1.init_map)
                    e2 = _concretize_sympy(cf2.expr, phase_init, cf2.init_map)
                    diff = sp.simplify(e1 - e2)
                except _SYMBOLIC_BESTEFFORT_EXC as exc:
                    logger.debug("assemble_candidates: diff failed: %s", exc)
                    continue
                if n_sym in diff.free_symbols:
                    continue
                gi = _ground_int(diff)
                if gi is not None:
                    emit(v1 == v2 if gi == 0 else v1 == v2 + z3.IntVal(gi))
                    continue
                # non-ground but both CFs are pure inits: skip tautologies
                merged_map = {**cf2.init_map, **cf1.init_map}
                z3_diff = _sympy_to_z3(diff, merged_map)
                if z3_diff is None:
                    continue
                try:
                    simplified = z3.simplify(z3_diff)
                    if phase_init:
                        simplified = z3.simplify(
                            z3.substitute(
                                simplified,
                                *[(k, val) for k, val in phase_init.items()],
                            )
                        )
                except z3.Z3Exception as exc:
                    logger.debug("assemble_candidates: simplify failed: %s", exc)
                    continue
                if z3.is_int_value(simplified):
                    const = simplified.as_long()
                    emit(v1 == v2 if const == 0 else v1 == v2 + z3.IntVal(const))

    # Deduplicate by sexpr string.
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

    When *initial_state* is known (e.g. from fact rules), starting branches
    whose guard is already UNSAT under that state are skipped -- they cannot
    be the entry phase and only produce noise candidates.
    """
    all_phases: list[Phase] = []
    all_boundaries: list[PhaseBoundary] = []
    for start in range(len(branches)):
        if initial_state:
            consistency = _branch_guard_consistent(branches[start], initial_state)
            if consistency is False:
                continue
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



def extract_concrete_inits(
    program: HornProgram,
    relation: z3.FuncDeclRef,
) -> dict[z3.ExprRef, z3.ExprRef]:
    """Harvest concrete initial values from fact rules for *relation*.

    When a fact assigns integer constants to the relation arguments
    (``(inv 0 5000)``), those constants become the phase-0 init_state so
    closed forms and boundaries can be concretized (e.g. n*=5000 instead of
    ``5000 - x0``).  Multiple facts: only keep values agreed by all facts;
    conflicting positions are left unconstrained.
    """
    agreed: dict[int, z3.ExprRef] | None = None  # position -> value
    arity = relation.arity()
    for rule in program.rules:
        if not rule.is_fact or rule.dst_relation.get_id() != relation.get_id():
            continue
        if len(rule.dst_args) != arity:
            continue
        pos_vals: dict[int, z3.ExprRef] = {}
        for i, arg in enumerate(rule.dst_args):
            # Prefer evaluating equalities in the fact body
            val = None
            body = rule.body
            conjuncts = list(body.children()) if z3.is_and(body) else [body]
            for c in conjuncts:
                if z3.is_eq(c):
                    lhs, rhs = c.arg(0), c.arg(1)
                    if lhs.get_id() == arg.get_id() and (
                        z3.is_int_value(rhs) or z3.is_rational_value(rhs)
                    ):
                        val = rhs
                        break
                    if rhs.get_id() == arg.get_id() and (
                        z3.is_int_value(lhs) or z3.is_rational_value(lhs)
                    ):
                        val = lhs
                        break
            if val is None and (z3.is_int_value(arg) or z3.is_rational_value(arg)):
                val = arg
            if val is not None:
                pos_vals[i] = val
        if agreed is None:
            agreed = pos_vals
        else:
            # intersection of agreed concrete values
            agreed = {
                i: v for i, v in agreed.items()
                if i in pos_vals and pos_vals[i].eq(v)
            }
    if not agreed:
        return {}
    # Map to a representative fact's dst_args / any rule's arg placeholders
    # Callers re-key onto pre_vars by position.
    return agreed


def _init_state_for_rule(
    program: HornProgram,
    rule: HornRule,
) -> dict[z3.ExprRef, z3.ExprRef]:
    """Build pre_var -> concrete value map for phase-0, when facts allow it."""
    if rule.src_relation is None:
        return {}
    by_pos = extract_concrete_inits(program, rule.src_relation)
    out: dict[z3.ExprRef, z3.ExprRef] = {}
    for i, pre in enumerate(rule.src_args):
        if i in by_pos:
            out[pre] = by_pos[i]
    return out


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

        branches = extract_mbp_guarded_branches(rule)
        if not branches:
            # Retain the syntactic flattener as a conservative fallback for
            # unsupported theories or QE failures.  The primary PhaseFit
            # path is MBP-based, matching ImplCheck.
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

        fact_init = _init_state_for_rule(self.program, rule)
        phases, boundaries = stitch_phases_from_all_starts(
            branches,
            pre_vars,
            post_to_pre,
            phase_budget=self.phase_budget,
            p_max=self.p_max,
            initial_state=fact_init or None,
        )
        raw_cands = assemble_candidates(
            phases, pre_vars, extra_atoms=extra, global_init=fact_init or None
        )

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
