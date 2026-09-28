"""ABMC-style loop acceleration, offered as the ``--accelerate-bmc`` option.

Bounded model checking finds unsafety by unrolling a program's transition
relation; a counterexample that only manifests after many loop iterations
needs a correspondingly large bound. Frohn/Giesl et al.'s "Accelerated
Bounded Model Checking" (FM 2024) tightens BMC by computing loop
"shortcuts" -- closed-form transitions that compress many iterations into
one SMT-visible step -- and splicing them into the search on the fly.

This module ports that idea into pyhorn's bounded explorer as a *static*
pre-pass: :func:`accelerate_program` looks at every self-loop rule in an
already-parsed :class:`~pyhorn_bnd.horn.HornProgram`, and for every branch
of that self-loop it can solve a closed form for, synthesizes an extra
:class:`~pyhorn_bnd.horn.HornRule` representing "n consecutive iterations
of this branch". The raw rule is replaced only after a separate SMT check
proves that the generated shortcuts cover every one-step transition of
that rule; otherwise the raw rule remains available as a conservative
fallback (see :func:`accelerate_program`).
:class:`~pyhorn_bnd.explorer.BoundedExplorer` needs no changes at all: it
already treats every entry of ``HornProgram.outgoing[relation]`` as an
interchangeable one-hop transition, so a trace search that happens to pick
the synthetic edge reaches a real iteration count of ``n`` at search depth
1 instead of depth ``n``.

Scope of this port:

  * Only ABMC's Requirement-1 case: a *singleton* cyclic suffix, i.e. one
    already-parsed, non-synthetic self-loop rule
    (``rule.is_inductive``, ``rule.src_relation is rule.dst_relation``).
    Because that is a static, syntactic property of a rule, every
    self-loop in the program can be accelerated once, up front, before
    any search happens -- unlike the paper's own online dependency-graph
    discovery, which pyhorn does not need here.
  * Internal ``ite``-branches inside one self-loop ARE supported: one
    shortcut rule is synthesized per feasible branch recovered from
    PhaseFit's ITE flattener, matching PhaseFit's own multi-phase view of a
    branching loop (e.g. "while below threshold, increment x; once at or
    above it, increment y instead" becomes two independent shortcuts).
  * Multi-rule / multi-predicate cycles (the paper's nested-loop case)
    are NOT supported -- that needs sequential composition of two
    transition formulas before handing them to PhaseFit's closed-form
    solver, which is a distinct, larger follow-up.
  * Only guards PhaseFit's closed-form/guard machinery can classify --
    either genuinely invariant across iterations (e.g. a branch that
    doesn't touch any variable the guard reads) or "monotonic" with an
    explicit crossover point -- are accelerated. Periodic guards, or
    updates past PhaseFit's affine/geometric/mod closed-form ceiling,
    silently fall back to plain unrolling for that branch. Candidate
    closed forms are independently checked against the extracted one-step
    branch transition before they are emitted.

None of this changes what BoundedExplorer can prove. An accelerated rule
is a semantically redundant extra edge in the same relation graph (every
state it reaches was already reachable via enough plain unrolling steps),
so soundness and completeness are exactly what they were before -- this
only changes how quickly a given bound reaches a given real iteration
count.

Two pieces of this module are shaped by a second paper, "Virtual
Counterexamples for Scalable Bug Finding" (VCEX), which represents a
counterexample as a closed-form function of a step index rather than an
explicit trace, validated by a constant number of SMT queries independent
of trace length. A synthesized shortcut rule here already *is* a
restricted instance of that idea -- ``n`` is VCEX's ``N``, each
``ClosedForm.expr`` is one component of its witness function ``f`` -- and
adopting two more of its ideas directly improved this module:

  * ``_validate_bound`` replaces trusting a proposed bound by
    construction (the direction-and-rounding case analysis this module
    used to rely on exclusively, and which is exactly where this
    session's tested bugs came from) with VCEX's own ``Validate``
    check: ask Z3 directly whether a counterexample iterate exists
    inside the claimed range, independent of how the bound was proposed.
    ``_propose_bound``/``_exact_affine_bound`` still do the proposing;
    they're just no longer trusted unchecked.
  * ``_validate_closed_form_anchor`` and ``_validate_closed_form_step`` apply
    the same idea to the synthesized trajectory itself: ``f(0)`` must be the
    real source state, and there must be no ``0 <= k < n`` where
    ``f(k) -> f(k+1)`` disagrees with the extracted branch update. This is
    essential because PhaseFit's per-variable closed forms were designed as
    invariant candidates, not as a proof of a simultaneous transition.
  * :func:`describe_witness` adopts VCEX's developer-facing report
    format -- the error depth ``N`` plus the per-variable closed-form
    function ``f`` -- for whatever counterexample ``BoundedExplorer``
    finds, instead of a bare rule-name sequence and a raw Z3 model dump.

VCEX's own synthesis strategies (SyGuS over a bitwise/ite grammar,
sampling-based PBE, and treating a CHC's predicate as part of an extended
state so one witness can span multiple predicates) are not adopted here
-- they'd extend *what* this module can accelerate (bitwise patterns
PhaseFit's closed-form solver can't derive; multi-rule cycles, which
remain this module's main open limitation) rather than *how soundly* it
checks what it already proposes, and are a distinct, larger follow-up.
"""

from __future__ import annotations

import logging
from dataclasses import dataclass, replace

import sympy as sp
from sympy.core.relational import Relational as _SpRelational
import z3
from z3.z3util import get_vars

from .horn import HornProgram, HornRule, _build_program
from .phasefit import (
    Branch,
    ClosedForm,
    _flatten_ite,
    _guard_to_sympy,
    _sympy_to_z3,
    _transition_formula,
    classify_guard,
    compute_branch_closed_forms,
    extract_guarded_branches,
)

logger = logging.getLogger(__name__)

# PhaseFit's own compute_closed_form / classify_guard each independently
# construct this exact symbol. sympy Symbol identity is (name, assumptions),
# so this has to match theirs exactly for substitutions and free_symbols
# checks against a ClosedForm's `.expr` to line up -- a mismatch here fails
# silently (classify_guard just reports "unknown") rather than raising.
_N = sp.Symbol("n", integer=True, nonnegative=True)

# Collapses redundant nested-ite artifacts (see _simplify_guard) before any
# guard reaches the bound derivation below.
_GUARD_SIMPLIFY_TACTIC = z3.Then("simplify", "propagate-ineqs", "ctx-solver-simplify")


@dataclass(frozen=True)
class AccelerationSummary:
    """Diagnostics for one :func:`accelerate_program` run.

    ``formulas_by_rule_id`` maps each shortcut's *final* ``rule_id`` (as
    it appears in the augmented program returned alongside this summary,
    and therefore in any trace ``BoundedExplorer`` finds) to its
    per-variable closed forms as ``(display_name, formula)`` pairs. This
    is what :func:`describe_witness` uses to turn a found counterexample
    into a VCEX-style report instead of a bare rule-name sequence.
    """

    inductive_rules_considered: int
    branches_considered: int
    shortcuts_added: int
    shortcut_rules: tuple[HornRule, ...]
    formulas_by_rule_id: dict[int, tuple[tuple[str, str], ...]]

    def describe(self) -> str:
        return (
            f"{self.inductive_rules_considered} self-loop rule(s), "
            f"{self.branches_considered} branch(es) considered, "
            f"{self.shortcuts_added} shortcut(s) added"
        )


def _simplify_guard(guard: z3.BoolRef) -> z3.BoolRef:
    """Collapse redundant structure PhaseFit's branch extraction can leave
    behind. A branch's guard is built by conjoining, for each ite in the
    rule, either the condition or its negation; for a multi-way nested ite
    (three or more phases) this can produce something like
    ``And(x0>=30, Not(And(x0>=15, Not(x0>=30))))`` where the second
    conjunct is already implied by the first. Left as-is, that nested
    ``Not(And(...))`` isn't a shape the bound derivation below
    recognises at all; simplified, it disappears entirely, leaving a
    plain conjunction of relational atoms. Falls back to the original
    guard, unsimplified, if the tactic can't run for any reason -- the
    only effect of skipping simplification is that some accelerable
    branches are conservatively left unaccelerated, never an unsound
    shortcut.

    A final plain ``z3.simplify`` pass mops up a residual
    ``ctx-solver-simplify`` can leave behind on deeper (4+ way) nested
    ite trees: a vacuously-true leftover like
    ``Not(And(False, Not(False)))`` that isn't itself further folded to
    a literal ``True``. Left in, that leaf isn't a shape
    ``_guard_to_sympy`` can translate at all (it's not a relational, and
    not one of And/Or/Not over one), so it silently kills the entire
    branch it's attached to -- found via testing a five-phase relay,
    where it happened on exactly one of five branches.
    """
    try:
        goals = _GUARD_SIMPLIFY_TACTIC(guard)
    except z3.Z3Exception:
        return guard
    if not goals:
        return guard
    disjuncts = [g[0] if len(g) == 1 else z3.And(*g) for g in goals if len(g) > 0]
    if not disjuncts:
        return z3.BoolVal(True)
    result = disjuncts[0] if len(disjuncts) == 1 else z3.Or(*disjuncts)
    return z3.simplify(result)


def _update_definition_info(
    rule: HornRule,
) -> tuple[set[int], dict[int, z3.ExprRef]] | None:
    """Return the equalities and substitutions that form the update chain.

    PhaseFit collects every top-level equality into a definition map.  That is
    fine for candidate mining, but acceleration cannot use the same shortcut:
    a source-state condition such as ``x == 0`` is a loop guard, not an update,
    and dropping it makes the synthesized transition strictly larger than the
    real one.

    Starting from the destination arguments, walk only equality definitions
    needed to express those destinations, following intermediate variables but
    never treating source-state variables as definitions.  Ambiguous duplicate
    definitions are rejected: callers then conservatively treat *all*
    equalities as guards, which normally makes that rule unaccelerable rather
    than risking an unsound shortcut.
    """
    tr = _transition_formula(rule)
    if tr is None:
        return set(), {}
    conjuncts = list(tr.children()) if z3.is_and(tr) else [tr]
    src_ids = {v.get_id() for v in rule.src_args}
    definitions: dict[int, tuple[z3.BoolRef, z3.ExprRef]] = {}
    for conjunct in conjuncts:
        if not z3.is_eq(conjunct):
            continue
        lhs, rhs = conjunct.arg(0), conjunct.arg(1)
        if not z3.is_const(lhs) or lhs.get_id() in src_ids:
            continue
        lhs_id = lhs.get_id()
        if lhs_id in definitions:
            return None
        definitions[lhs_id] = (conjunct, rhs)

    selected: set[int] = set()
    selected_defs: dict[int, z3.ExprRef] = {}
    visiting: set[int] = set()
    visited: set[int] = set()

    def visit(var_id: int) -> bool:
        if var_id in src_ids or var_id not in definitions:
            return True
        if var_id in visiting:
            return False
        if var_id in visited:
            return True
        visiting.add(var_id)
        conjunct, rhs = definitions[var_id]
        selected.add(conjunct.get_id())
        selected_defs[var_id] = rhs
        for dep in get_vars(rhs):
            dep_id = dep.get_id()
            if dep_id not in src_ids and dep_id in definitions and not visit(dep_id):
                return False
        visiting.remove(var_id)
        visited.add(var_id)
        return True

    for dst in rule.dst_args:
        if not visit(dst.get_id()):
            return None
    return selected, selected_defs


def _expand_update_definitions(
    expr: z3.ExprRef,
    definitions: dict[int, z3.ExprRef],
    src_ids: set[int],
    *,
    depth: int = 32,
) -> z3.ExprRef | None:
    """Inline selected update definitions into a residual transition guard."""
    if depth <= 0:
        # A very deep (or cyclic, despite the earlier cycle check) definition
        # chain is not a reason to guess.  If a selected definition is still
        # present, fail closed and let the caller skip acceleration.
        if any(v.get_id() in definitions for v in get_vars(expr)):
            return None
        return expr
    substitutions: list[tuple[z3.ExprRef, z3.ExprRef]] = []
    for var in get_vars(expr):
        var_id = var.get_id()
        if var_id in src_ids or var_id not in definitions:
            continue
        substitutions.append((var, definitions[var_id]))
    if not substitutions:
        return expr
    try:
        expanded = z3.substitute(expr, *substitutions)
    except z3.Z3Exception:
        return None
    return _expand_update_definitions(
        expanded, definitions, src_ids, depth=depth - 1
    )


def _loop_guard_atoms(rule: HornRule) -> list[z3.BoolRef] | None:
    """Transition conjuncts that are not proven update definitions.

    ``_transition_formula`` strips the relation atoms out of ``rule.body``.
    Equalities are retained unless :func:`_update_definition_info` proves they
    belong to the destination update chain. In particular, source-state
    equalities such as ``x == 0`` remain loop guards. Residual guards are
    expanded through selected intermediate/destination definitions, so a
    condition such as ``h < 10`` with ``h = x + 1`` is checked as
    ``x + 1 < 10`` on every virtual iteration rather than treating ``h`` as a
    loop-invariant auxiliary value.
    """
    tr = _transition_formula(rule)
    if tr is None:
        return []
    conjuncts = list(tr.children()) if z3.is_and(tr) else [tr]
    info = _update_definition_info(rule)
    if info is None:
        return None
    update_ids, definitions = info
    src_ids = {v.get_id() for v in rule.src_args}
    guards: list[z3.BoolRef] = []
    for conjunct in conjuncts:
        if conjunct.get_id() in update_ids:
            continue
        expanded = _expand_update_definitions(conjunct, definitions, src_ids)
        if expanded is None:
            return None
        guard = _simplify_guard(expanded)
        if not z3.is_true(z3.simplify(guard)):
            guards.append(guard)
    return guards


def _branch_guard_atoms(branch: Branch) -> list[z3.BoolRef]:
    guard = _simplify_guard(branch.guard)
    if z3.is_true(guard):
        return []
    atoms = list(guard.children()) if z3.is_and(guard) else [guard]
    return [a for a in atoms if not z3.is_true(z3.simplify(a))]


_MAX_ACCEL_PARTIAL_BRANCHES = 64


def _extract_acceleration_branches(rule: HornRule) -> list[Branch]:
    """Extract feasible ITE branches without capping the raw Cartesian product.

    PhaseFit's syntactic fallback computes the full per-variable Cartesian
    product *before* checking guard feasibility and deliberately truncates when
    that raw product exceeds 64.  Shared phase conditions can make the raw
    product look large even though only a handful of combinations are
    satisfiable (the five-phase relay benchmark has 108 syntactic combinations
    but only five real phases).

    For acceleration, combine variables incrementally and prune UNSAT guard
    combinations after every variable.  This recovers those synchronized
    phases without lifting PhaseFit's global safety valve.  If more than 64
    *feasible partial* combinations survive, fall back to PhaseFit's bounded
    extractor; the later one-step coverage proof then guarantees that such an
    incomplete branch set can never replace the raw loop.
    """
    if not rule.is_inductive:
        return []
    info = _update_definition_info(rule)
    if info is None:
        return []
    _update_ids, definitions = info
    src_ids = {v.get_id() for v in rule.src_args}

    per_var: list[tuple[z3.ExprRef, list[tuple[z3.BoolRef, z3.ExprRef]]]] = []
    for index, dst in enumerate(rule.dst_args):
        rhs = definitions.get(dst.get_id())
        if rhs is None:
            src = rule.src_args[index] if index < len(rule.src_args) else dst
            per_var.append((dst, [(z3.BoolVal(True), src)]))
            continue
        pure = _expand_update_definitions(rhs, definitions, src_ids)
        if pure is None:
            return extract_guarded_branches(rule)
        leaves: list[tuple[z3.BoolRef, z3.ExprRef]] = []
        for guard, update in _flatten_ite(pure):
            expanded_guard = _expand_update_definitions(guard, definitions, src_ids)
            expanded_update = _expand_update_definitions(update, definitions, src_ids)
            if expanded_guard is None or expanded_update is None:
                return extract_guarded_branches(rule)
            leaves.append((_simplify_guard(expanded_guard), expanded_update))
        per_var.append((dst, leaves))

    partials: list[tuple[z3.BoolRef, dict[z3.ExprRef, z3.ExprRef]]] = [
        (z3.BoolVal(True), {})
    ]
    for dst, leaves in per_var:
        next_partials: list[tuple[z3.BoolRef, dict[z3.ExprRef, z3.ExprRef]]] = []
        for partial_guard, partial_updates in partials:
            for leaf_guard, update in leaves:
                guard = _simplify_guard(z3.And(partial_guard, leaf_guard))
                solver = z3.Solver()
                solver.set("timeout", 80)
                solver.add(guard)
                try:
                    if solver.check() == z3.unsat:
                        continue
                except z3.Z3Exception:
                    pass
                updates = dict(partial_updates)
                updates[dst] = update
                next_partials.append((guard, updates))
                if len(next_partials) > _MAX_ACCEL_PARTIAL_BRANCHES:
                    logger.warning(
                        "accelerate_bmc: more than %d feasible partial ITE "
                        "branches for %s; using PhaseFit's bounded fallback",
                        _MAX_ACCEL_PARTIAL_BRANCHES,
                        rule.short(),
                    )
                    return extract_guarded_branches(rule)
        partials = next_partials
        if not partials:
            return []

    return [Branch(guard=guard, updates=updates) for guard, updates in partials]


def _validate_branch_abstraction(rule: HornRule, branch: Branch) -> bool:
    """Prove that one extracted branch is a subset of the original rule.

    PhaseFit's branch extractor was designed for candidate mining, so the
    acceleration layer does not trust its output as transition semantics by
    construction.  Eliminate the acyclic update definitions from the original
    transition, then ask whether the branch guard/update can violate that
    normalized transition.  UNSAT establishes the one-step implication for
    all source states and rule-local auxiliary values.

    Destination arguments without a selected equality definition are left
    unconstrained in the normalized original transition.  PhaseFit represents
    those as identities, which is a sound subset and therefore still passes
    this check.
    """
    info = _update_definition_info(rule)
    if info is None:
        return False
    _update_ids, definitions = info
    src_ids = {v.get_id() for v in rule.src_args}
    loop_guards = _loop_guard_atoms(rule)
    if loop_guards is None:
        return False

    original_updates: list[z3.BoolRef] = []
    for dst in rule.dst_args:
        if dst.get_id() not in definitions:
            continue
        expanded = _expand_update_definitions(dst, definitions, src_ids)
        if expanded is None:
            return False
        original_updates.append(dst == expanded)

    branch_updates = [post == update for post, update in branch.updates.items()]
    branch_formula = z3.And(branch.guard, *loop_guards, *branch_updates)
    normalized_original = z3.And(*loop_guards, *original_updates)
    solver = z3.Solver()
    solver.set("timeout", _CHECK_TIMEOUT_MS)
    solver.add(branch_formula)
    solver.add(z3.Not(normalized_original))
    try:
        return solver.check() == z3.unsat
    except z3.Z3Exception:
        return False


# sympy relational classes, used by _is_decreasing_truth below. Bound as
# module-level names once so isinstance checks don't repeatedly do
# attribute lookups on the sp module.
_SP_LT, _SP_LE, _SP_GT, _SP_GE = (
    sp.StrictLessThan,
    sp.LessThan,
    sp.StrictGreaterThan,
    sp.GreaterThan,
)


def _peel_not(pred: sp.Basic) -> tuple[sp.Basic, bool]:
    negate = False
    while isinstance(pred, sp.Not):
        negate = not negate
        pred = pred.args[0]
    return pred, negate


def _is_decreasing_truth(pred: sp.Basic) -> bool:
    """True if *pred* (already substituted with closed forms, so a
    predicate purely in ``_N`` and other free symbols) is sound to treat
    as "true for iterates 0..k-1, false from iterate k on" for some k --
    the only shape it's sound to accelerate a guard on. A conjunction of
    such atoms has the same shape (true until the FIRST one goes false),
    so recurses through ``And``; anything built from ``Or`` is rejected
    outright rather than risked, since one true disjunct can mask another
    that would make the overall truth non-monotonic.

    This function exists because trusting a "this guard eventually
    becomes false" classification without checking the *direction* is
    exactly how a genuinely n-invariant-or-increasing guard (e.g. an
    always-true `x0 >= 0` on a variable that only ever increases) can end
    up with an inverted, self-contradictory bound -- found via testing,
    not hypothetically: see the accompanying benchmark notes.
    """
    return _affine_guard_direction(pred) == "decreasing"


def _is_increasing_truth(pred: sp.Basic) -> bool:
    """Mirror of :func:`_is_decreasing_truth`: true if *pred* only ever
    becomes MORE satisfied as the iterate index grows (e.g. `x0 >= 15` on
    a variable that only increases). Such a guard needs no bound on n at
    all -- if it held once, at the very first application, it holds for
    every later one -- but it's a genuinely different case from a guard
    that doesn't depend on n at all (the ``_N not in pred.free_symbols``
    check in ``_bound_for_guard``), and conflating the two by e.g. just
    accepting any guard that doesn't need an upper bound would blur past
    the direction check that matters for soundness.
    """
    return _affine_guard_direction(pred) == "increasing"


def _affine_guard_direction(pred: sp.Basic) -> str | None:
    """Returns ``"decreasing"``, ``"increasing"``, or ``None`` (mixed,
    unsupported shape, or not affine in ``_N``). A conjunction is
    decreasing if every conjunct is (true until the first one fails) and
    increasing if every conjunct is (true from the point every conjunct
    has individually become true on, i.e. from the max of their
    individual thresholds -- still exactly representable as "assert every
    raw guard holds initially", since each conjunct's own increasing-
    truth precondition composes with And the same way).
    """
    if isinstance(pred, sp.And):
        directions = {_affine_guard_direction(p) for p in pred.args}
        return directions.pop() if len(directions) == 1 else None
    inner, negate = _peel_not(pred)
    if isinstance(inner, _SP_LT):
        op = "ge" if negate else "lt"
    elif isinstance(inner, _SP_LE):
        op = "gt" if negate else "le"
    elif isinstance(inner, _SP_GT):
        op = "le" if negate else "gt"
    elif isinstance(inner, _SP_GE):
        op = "lt" if negate else "ge"
    else:
        return None  # Eq/Ne/Or/anything else: not a supported shape
    expr = sp.expand(inner.lhs - inner.rhs)
    if _N not in expr.free_symbols:
        return None  # shouldn't happen; caller already filtered on this
    coeff = sp.diff(expr, _N)
    if not coeff.is_number or _N in coeff.free_symbols:
        return None  # not affine in n, or a symbolic (non-constant) rate
    if op in ("lt", "le"):
        # expr < 0 / expr <= 0: grows with n (coeff>0) -> decreasing truth
        # (eventually >= 0); shrinks with n (coeff<0) -> increasing truth.
        if coeff > 0:
            return "decreasing"
        if coeff < 0:
            return "increasing"
        return None
    # "gt"/"ge": expr > 0 / expr >= 0: shrinks with n -> decreasing truth;
    # grows with n -> increasing truth.
    if coeff < 0:
        return "decreasing"
    if coeff > 0:
        return "increasing"
    return None


def _sympy_pred_to_z3(
    pred: sp.Basic, reverse_map: dict[sp.Symbol, z3.ExprRef]
) -> z3.BoolRef | None:
    """Boolean-layer counterpart to PhaseFit's ``_sympy_to_z3`` (which only
    handles arithmetic expressions): converts a sympy tree of
    And/Or/Not/relationals back to a Z3 formula, calling ``_sympy_to_z3``
    for the arithmetic leaves.
    """
    if isinstance(pred, sp.And):
        parts = [_sympy_pred_to_z3(p, reverse_map) for p in pred.args]
        return None if any(p is None for p in parts) else z3.And(*parts)
    if isinstance(pred, sp.Or):
        parts = [_sympy_pred_to_z3(p, reverse_map) for p in pred.args]
        return None if any(p is None for p in parts) else z3.Or(*parts)
    if isinstance(pred, sp.Not):
        inner = _sympy_pred_to_z3(pred.args[0], reverse_map)
        return None if inner is None else z3.Not(inner)
    if isinstance(pred, _SpRelational):
        lhs = _sympy_to_z3(pred.lhs, reverse_map)
        rhs = _sympy_to_z3(pred.rhs, reverse_map)
        if lhs is None or rhs is None:
            return None
        if isinstance(pred, sp.Eq):
            return lhs == rhs
        if isinstance(pred, sp.Ne):
            return lhs != rhs
        if isinstance(pred, _SP_LT):
            return lhs < rhs
        if isinstance(pred, _SP_LE):
            return lhs <= rhs
        if isinstance(pred, _SP_GT):
            return lhs > rhs
        if isinstance(pred, _SP_GE):
            return lhs >= rhs
    if pred is sp.true:
        return z3.BoolVal(True)
    if pred is sp.false:
        return z3.BoolVal(False)
    return None


def _exact_affine_bound(
    pred: sp.Basic,
    n_var: z3.ArithRef,
    reverse_map: dict[sp.Symbol, z3.ExprRef],
) -> list[z3.BoolRef] | None:
    """Exact (no floor/ceiling rounding) side-condition equivalent to
    "*pred* holds for iterates 0..n_var-1", for a *pred* confirmed
    decreasing-truth by :func:`_is_decreasing_truth`.

    This deliberately avoids solving for an explicit closed-form crossover
    point algebraically (the approach that produces a real/fractional
    value like ``38.46`` for an integer problem, which then either over-
    or under-shoots by one depending on rounding direction -- found via
    testing on a non-unit-step and on a non-strict guard, both of which
    are common shapes, not edge cases). Instead it asserts the guard,
    evaluated at iterate ``n_var - 1`` via Z3's own integer arithmetic,
    directly. Given the confirmed decreasing-truth direction, that single
    condition is exactly equivalent to every earlier iterate also
    satisfying the guard, with no rounding step to get wrong.
    """
    if not _is_decreasing_truth(pred):
        return None
    shifted_map = dict(reverse_map)
    shifted_map[_N] = n_var - 1
    z3_pred = _sympy_pred_to_z3(pred, shifted_map)
    if z3_pred is None:
        return None
    return [z3_pred]


_CHECK_TIMEOUT_MS = 2_000


def _validate_bound(
    pred: sp.Basic,
    n_var: z3.ArithRef,
    reverse_map: dict[sp.Symbol, z3.ExprRef],
    bound_atoms: list[z3.BoolRef],
) -> bool:
    """VCEX-style ``Validate``: confirm a proposed bound really does make
    the guard hold for every iterate ``0..n_var-1``, via one direct
    semantic query, independent of how the bound was derived.

    "Virtual Counterexamples" (the paper this module's design notes
    reference) validates a candidate witness function by checking
    ``exists k. 0<=k<N and not tr(f(k),f(k+1))`` is UNSAT -- a single
    query that doesn't care how the candidate function was produced, only
    whether it's actually correct. This is that same check, applied to a
    candidate loop-guard bound instead of a whole trajectory: does there
    exist an iterate index ``k`` inside the proposed range where the
    guard, evaluated at that iterate via the branch's own closed forms,
    fails to hold?

    This replaces trusting ``_exact_affine_bound``'s or
    ``classify_guard``'s derivation by construction. Both of those
    propose a bound; this is the independent check that either confirms
    or refutes the proposal, and it is the reason this module has just
    one place that needs to be correct rather than one per derivation
    path. It would have caught both bugs this module's regression tests
    now cover (the off-by-one on non-strict/non-unit-step guards, and the
    self-contradictory bound on an increasing-truth guard) without
    needing either bug's specific fix to already be known -- it just asks
    Z3 whether the claim is true.
    """
    k_var = z3.Int(f"__accel_check_k_{id(n_var)}")
    shifted_map = dict(reverse_map)
    shifted_map[_N] = k_var
    pred_at_k = _sympy_pred_to_z3(pred, shifted_map)
    if pred_at_k is None:
        return False
    solver = z3.Solver()
    solver.set("timeout", _CHECK_TIMEOUT_MS)
    solver.add(n_var > 0, *bound_atoms)
    solver.add(0 <= k_var, k_var < n_var)
    solver.add(z3.Not(pred_at_k))
    try:
        return solver.check() == z3.unsat
    except z3.Z3Exception:
        return False  # can't confirm: treat the proposal as unvalidated


def _propose_bound(
    guard: z3.BoolRef,
    pred: sp.Basic,
    closed_forms: dict[z3.ExprRef, ClosedForm],
    n_var: z3.ArithRef,
    reverse_map: dict[sp.Symbol, z3.ExprRef],
) -> list[z3.BoolRef] | None:
    """Propose a side-condition on ``n_var`` for *guard* to hold across
    every iterate -- the "synthesis" half of propose/validate. May be
    wrong; ``_bound_for_guard`` always re-checks the result with
    :func:`_validate_bound` before trusting it, so a mistake here costs a
    missed acceleration opportunity, never an unsound one.
    """
    if _is_increasing_truth(pred):
        # Only ever becomes MORE satisfied as the iterate index grows (the
        # `x0 >= 15` half of a phase boundary on a variable that only
        # increases, for instance) -- if it held at the very first
        # application it holds at every later one, so assert it as a
        # precondition over the initial state rather than deriving any
        # bound on n at all.
        return [guard]

    exact = _exact_affine_bound(pred, n_var, reverse_map)
    if exact is not None:
        return exact

    # Fall back to PhaseFit's own guard classifier for shapes the exact
    # affine path above doesn't confidently handle (non-linear updates
    # PhaseFit itself can still classify, e.g. via its periodicity probe).
    kind, info = classify_guard(guard, closed_forms)
    if kind == "monotonic":
        bound = (
            z3.IntVal(info)
            if isinstance(info, int)
            else _sympy_to_z3(info, reverse_map)
        )
        if bound is None:
            return None
        return [n_var <= bound]
    if kind == "constant" and info is True:
        return []
    # "constant" with info is False (guard identically false), "periodic",
    # or "unknown": no candidate to propose from this guard.
    return None


def _bound_for_guard(
    guard: z3.BoolRef,
    closed_forms: dict[z3.ExprRef, ClosedForm],
    n_var: z3.ArithRef,
    reverse_map: dict[sp.Symbol, z3.ExprRef],
) -> list[z3.BoolRef] | None:
    """Sound side-condition(s) on ``n_var`` so *guard* holds for iterates
    ``0..n_var-1``, or ``None`` if this guard can't be bounded soundly
    with what's available here. Proposes a candidate via
    :func:`_propose_bound`, then re-checks it via :func:`_validate_bound`
    before returning it -- see both docstrings for why the split matters.
    """
    pred = _guard_to_sympy(guard, closed_forms, _N)
    if pred is None:
        return None
    if _N not in pred.free_symbols:
        # This branch's own closed forms don't make the guard's truth
        # depend on how many times it's applied (e.g. every variable the
        # guard reads has an identity closed form under this branch, or
        # the guard doesn't mention a variable the loop touches at all) --
        # so if it held for the very first application, it holds for
        # every subsequent one. This is an exact syntactic fact (n
        # provably doesn't appear), not a derived claim, so it skips
        # _validate_bound rather than needing it confirmed.
        return [guard]

    candidate = _propose_bound(guard, pred, closed_forms, n_var, reverse_map)
    if candidate is None:
        return None
    if not _validate_bound(pred, n_var, reverse_map, candidate):
        return None
    return candidate


def _validate_closed_form_anchor(
    rule: HornRule,
    closed_forms: dict[z3.ExprRef, ClosedForm],
    reverse_map: dict[sp.Symbol, z3.ExprRef],
) -> bool:
    """Prove that every closed form denotes the actual source state at n=0.

    PhaseFit was originally written for invariant candidate mining, not for
    transition rewriting, and some of its best-effort forms intentionally do
    not encode the recurrence's base case (for example ``x' = 7`` may be
    represented simply as the constant ``7``).  Such a form is useful for
    mining but cannot serve as a virtual execution trajectory unless
    ``f(0) == x``.  Reject it here rather than trying to patch the trajectory
    with an ite that the rest of the symbolic pipeline was not designed for.
    """
    at_zero = dict(reverse_map)
    at_zero[_N] = z3.IntVal(0)
    solver = z3.Solver()
    solver.set("timeout", _CHECK_TIMEOUT_MS)
    mismatches: list[z3.BoolRef] = []
    for src_arg in rule.src_args:
        cf = closed_forms[src_arg]
        value = _sympy_to_z3(cf.expr, at_zero)
        if value is None:
            return False
        mismatches.append(value != src_arg)
    if not mismatches:
        return True
    solver.add(z3.Or(*mismatches))
    try:
        return solver.check() == z3.unsat
    except z3.Z3Exception:
        return False


def _validate_closed_form_step(
    rule: HornRule,
    branch: Branch,
    closed_forms: dict[z3.ExprRef, ClosedForm],
    n_var: z3.ArithRef,
    reverse_map: dict[sp.Symbol, z3.ExprRef],
    bound_atoms: list[z3.BoolRef],
) -> bool:
    """Prove that the proposed closed forms satisfy one branch step at every k.

    This is the transition-level counterpart of :func:`_validate_bound`.
    It checks for a witness ``0 <= k < n`` where the candidate trajectory's
    state at ``k+1`` disagrees with the branch update applied to its state at
    ``k``.  UNSAT means the recurrence really is a repeated execution of this
    branch for every shortcut admitted by ``bound_atoms``.

    The check is what prevents PhaseFit's per-variable solver from being used
    unsafely on coupled recurrences.  For example, independently solving
    ``x' = x + y`` and ``y' = y + 1`` treats ``y`` as fixed while deriving
    ``x``; this query finds the mismatch at k=1 and rejects the shortcut.
    """
    k_var = z3.Int(f"__accel_step_k_{id(n_var)}")
    at_k = dict(reverse_map)
    at_k[_N] = k_var
    at_k1 = dict(reverse_map)
    at_k1[_N] = k_var + 1

    state_at_k: list[tuple[z3.ExprRef, z3.ExprRef]] = []
    next_by_src_id: dict[int, z3.ExprRef] = {}
    for src_arg in rule.src_args:
        cf = closed_forms[src_arg]
        current = _sympy_to_z3(cf.expr, at_k)
        nxt = _sympy_to_z3(cf.expr, at_k1)
        if current is None or nxt is None:
            return False
        state_at_k.append((src_arg, current))
        next_by_src_id[src_arg.get_id()] = nxt

    post_to_pre = dict(zip(rule.dst_args, rule.src_args, strict=True))
    mismatches: list[z3.BoolRef] = []
    for post_var, update in branch.updates.items():
        pre_var = post_to_pre.get(post_var)
        if pre_var is None:
            return False
        expected_next = next_by_src_id.get(pre_var.get_id())
        if expected_next is None:
            return False
        try:
            update_at_k = z3.substitute(update, *state_at_k)
        except z3.Z3Exception:
            return False
        mismatches.append(expected_next != update_at_k)

    if not mismatches:
        return False
    solver = z3.Solver()
    solver.set("timeout", _CHECK_TIMEOUT_MS)
    solver.add(n_var > 0, *bound_atoms)
    solver.add(0 <= k_var, k_var < n_var)
    solver.add(z3.Or(*mismatches))
    try:
        return solver.check() == z3.unsat
    except z3.Z3Exception:
        return False


def _shortcuts_cover_rule_one_step(
    rule: HornRule,
    shortcuts: list[HornRule],
) -> bool:
    """Prove that the shortcuts cover every concrete one-step transition.

    Branch extraction is deliberately best-effort: it caps large Cartesian
    products and may deduplicate branches that share updates.  Therefore the
    number of returned branches is not evidence of completeness.  Before the
    raw rule is removed, ask Z3 directly whether an original one-step
    transition exists that is not represented by any shortcut instantiated at
    ``n = 1``.  Only UNSAT permits replacement; SAT or UNKNOWN keeps the raw
    rule alongside the shortcuts.
    """
    if not shortcuts:
        return False
    transition = _transition_formula(rule)
    if transition is None:
        return False
    one_step_shortcuts: list[z3.BoolRef] = []
    for shortcut in shortcuts:
        if not shortcut.rule_vars:
            return False
        n_var = shortcut.rule_vars[-1]
        try:
            one_step_shortcuts.append(
                z3.substitute(shortcut.body, (n_var, z3.IntVal(1)))
            )
        except z3.Z3Exception:
            return False
    solver = z3.Solver()
    solver.set("timeout", _CHECK_TIMEOUT_MS)
    solver.add(transition)
    solver.add(z3.Not(z3.Or(*one_step_shortcuts)))
    try:
        return solver.check() == z3.unsat
    except z3.Z3Exception:
        return False


def _display_name(z3_var: z3.ExprRef) -> str:
    """Best-effort recovery of a variable's original source name from
    pyhorn's internal, decorated SSA-style names (e.g.
    ``__pyhorn_r1_0_0_x0`` -> ``x0``). Used only for the human-readable
    witness report below; never affects any solver query, so getting this
    wrong in an unusual case costs readability, not correctness.
    """
    name = str(z3_var)
    return name.rsplit("_", 1)[-1] if "_" in name else name


def _pretty_closed_form(
    var: z3.ExprRef, closed_forms: dict[z3.ExprRef, ClosedForm]
) -> str:
    """Render one variable's closed form with source-like names, e.g.
    ``x0 + n`` instead of ``__pyhorn_r1_0_0_x0_0 + n``. Best-effort
    formatting for the witness report; ``n`` always refers to how many
    times *this* shortcut is applied, matching its meaning in the
    synthesized rule's own body.
    """
    subs: dict[sp.Symbol, sp.Symbol] = {}
    for other_cf in closed_forms.values():
        for sym, z3_val in other_cf.init_map.items():
            if isinstance(z3_val, z3.ExprRef) and z3.is_const(z3_val):
                subs[sym] = sp.Symbol(_display_name(z3_val))
    return str(closed_forms[var].expr.subs(subs))

def _accelerate_branch(
    rule: HornRule, branch: Branch, *, synthetic_rule_id: int
) -> tuple[HornRule, tuple[tuple[str, str], ...]] | None:
    """Attempt accel([rule], branch) -- one closed-form shortcut for a
    single self-loop taking a single (possibly ite-selected) branch, n
    consecutive times. Returns None if PhaseFit's closed-form machinery
    can't solve this branch's recurrence or classify one of its guards;
    callers must treat that exactly like LoAT treats a non-polynomial
    acceleration result and fall back to plain unrolling for it.

    On success, also returns the per-variable closed forms as
    ``(display_name, formula)`` string pairs, in ``rule.src_args`` order
    -- purely for the human-readable witness report (see
    ``describe_witness`` below); the synthesized ``HornRule`` itself is
    unaffected by this and remains the only thing any solver query ever
    sees.
    """
    definition_info = _update_definition_info(rule)
    if definition_info is None:
        return None
    _definition_conjunct_ids, selected_definitions = definition_info
    selected_definition_ids = set(selected_definitions)
    # PhaseFit's own _fully_expand() is depth-bounded because its normal use is
    # best-effort candidate mining.  A residual selected temporary in a branch
    # update/guard is not acceptable for transition rewriting: treating that
    # temporary as one fixed shortcut-local value could fail to reproduce its
    # per-iteration definition.  Fail closed if expansion was incomplete.
    for expr in (branch.guard, *branch.updates.values()):
        if any(v.get_id() in selected_definition_ids for v in get_vars(expr)):
            return None
    if not _validate_branch_abstraction(rule, branch):
        return None

    post_to_pre = dict(zip(rule.dst_args, rule.src_args, strict=True))
    closed_forms = compute_branch_closed_forms(
        branch, list(rule.src_args), post_to_pre
    )
    if len(closed_forms) != len(rule.src_args):
        return None

    n_var = z3.Int(f"__accel_n_{synthetic_rule_id}")
    reverse_map: dict[sp.Symbol, z3.ExprRef] = {_N: n_var}
    for cf in closed_forms.values():
        reverse_map.update(cf.init_map)

    if not _validate_closed_form_anchor(rule, closed_forms, reverse_map):
        return None

    loop_guards = _loop_guard_atoms(rule)
    if loop_guards is None:
        return None
    bound_atoms: list[z3.BoolRef] = []
    for guard in (*loop_guards, *_branch_guard_atoms(branch)):
        atoms = _bound_for_guard(guard, closed_forms, n_var, reverse_map)
        if atoms is None:
            return None
        bound_atoms.extend(atoms)

    if not _validate_closed_form_step(
        rule, branch, closed_forms, n_var, reverse_map, bound_atoms
    ):
        return None

    dst_updates: list[z3.BoolRef] = []
    formulas: list[tuple[str, str]] = []
    for src_arg, dst_arg in zip(rule.src_args, rule.dst_args, strict=True):
        cf = closed_forms[src_arg]
        value = _sympy_to_z3(cf.expr, reverse_map)
        if value is None:
            return None
        dst_updates.append(dst_arg == value)
        formulas.append(
            (_display_name(dst_arg), _pretty_closed_form(src_arg, closed_forms))
        )

    body = z3.simplify(z3.And(n_var > 0, *bound_atoms, *dst_updates))
    learned = HornRule(
        rule_id=synthetic_rule_id,
        original_rule_id=rule.original_rule_id,
        body=body,
        rule_vars=(*rule.rule_vars, n_var),
        src_relation=rule.src_relation,
        src_args=rule.src_args,
        dst_relation=rule.dst_relation,
        dst_args=rule.dst_args,
        is_fact=False,
        is_query=False,
        is_inductive=True,
    )
    return learned, tuple(formulas)


def accelerate_program(
    program: HornProgram,
) -> tuple[HornProgram, AccelerationSummary]:
    """Add one synthetic shortcut rule per accelerable self-loop branch.

    Returns ``(augmented_program, summary)``. ``augmented_program`` is
    ``program`` itself, unchanged, if no shortcut could be derived.

    The raw rule is dropped only if :func:`_shortcuts_cover_rule_one_step`
    proves, with an independent SMT query, that every original one-step
    transition is represented by some shortcut instantiated at ``n = 1``.
    This matters because PhaseFit's branch extractor is intentionally
    best-effort: it caps large Cartesian products and may deduplicate
    branches. Counting extracted branches is therefore not a sound coverage
    test. If coverage cannot be proved (SAT, UNKNOWN, timeout, or an
    unsupported shape), the raw rule is kept and the successful shortcuts
    are merely added alongside it.

    Keeping both forms can increase BoundedExplorer's branching factor, so
    the coverage proof still enables the previous replacement optimization
    on ordinary fully-covered loops without making correctness depend on
    branch-enumeration heuristics.
    """
    next_id = len(program.rules)
    shortcuts_by_rule_id: dict[int, list[HornRule]] = {}
    formulas_by_synthetic_id: dict[int, tuple[tuple[str, str], ...]] = {}
    branches_considered = 0
    inductive_rules = [rule for rule in program.rules if rule.is_inductive]

    for rule in inductive_rules:
        branches = _extract_acceleration_branches(rule)
        for branch in branches:
            branches_considered += 1
            try:
                result = _accelerate_branch(rule, branch, synthetic_rule_id=next_id)
            except z3.Z3Exception as exc:
                # Defensive: a malformed or unusual rule shape (e.g. an
                # exotic array/string self-loop PhaseFit's translators
                # weren't built for) should fall back to plain unrolling
                # for this branch, not abort the whole run.
                logger.debug(
                    "accelerate_bmc: skipping %s branch (%s)", rule.short(), exc
                )
                result = None
            if result is not None:
                learned, formulas = result
                shortcuts_by_rule_id.setdefault(rule.rule_id, []).append(learned)
                formulas_by_synthetic_id[learned.rule_id] = formulas
                next_id += 1

    shortcuts = [
        learned
        for learned_for_rule in shortcuts_by_rule_id.values()
        for learned in learned_for_rule
    ]
    if not shortcuts:
        return program, AccelerationSummary(
            inductive_rules_considered=len(inductive_rules),
            branches_considered=branches_considered,
            shortcuts_added=0,
            shortcut_rules=(),
            formulas_by_rule_id={},
        )

    rule_by_id = {rule.rule_id: rule for rule in program.rules}
    fully_replaced_rule_ids = {
        rule_id
        for rule_id, learned_for_rule in shortcuts_by_rule_id.items()
        if (original := rule_by_id.get(rule_id)) is not None
        and _shortcuts_cover_rule_one_step(original, learned_for_rule)
    }
    kept_rules = [
        rule for rule in program.rules if rule.rule_id not in fully_replaced_rule_ids
    ]
    final_rules = [
        replace(rule, rule_id=index)
        for index, rule in enumerate(kept_rules + shortcuts)
    ]
    # Renumbering shifts every shortcut's rule_id; formulas_by_synthetic_id
    # was keyed by the pre-renumber id, so re-key it against the actual
    # rules that end up in the augmented program (final_shortcuts is in
    # the same order as `shortcuts`, since enumerate() preserves it).
    final_shortcuts = tuple(final_rules[len(kept_rules) :])
    formulas_by_rule_id = {
        new_rule.rule_id: formulas_by_synthetic_id[old_rule.rule_id]
        for old_rule, new_rule in zip(shortcuts, final_shortcuts, strict=True)
    }

    summary = AccelerationSummary(
        inductive_rules_considered=len(inductive_rules),
        branches_considered=branches_considered,
        shortcuts_added=len(shortcuts),
        shortcut_rules=final_shortcuts,
        formulas_by_rule_id=formulas_by_rule_id,
    )
    augmented = _build_program(
        program.source_path,
        final_rules,
        program.query_relations,
        sliced=program.sliced,
    )
    return augmented, summary


def describe_witness(
    trace: tuple[HornRule, ...],
    model: z3.ModelRef,
    fresh_rule_vars_by_step: tuple[tuple[z3.ExprRef, ...], ...],
    summary: AccelerationSummary,
) -> str:
    """Render a found counterexample as a VCEX-style witness report: the
    real iteration count ``N`` (which can be astronomically larger than
    the trace's own length, since each accelerated step stands in for
    however many real iterations its ``n`` took), and, for every
    accelerated step, which branch fired, how many times, and its
    per-variable closed form -- instead of a bare sequence of rule names
    and a raw model dump.

    ``fresh_rule_vars_by_step`` must line up with ``trace``: for step
    ``i``, ``fresh_rule_vars_by_step[i]`` is that step's freshened copy of
    ``trace[i].rule_vars`` (``VerificationCondition.steps[i].fresh_rule_vars``
    in the caller), used to look up the concrete value an accelerated
    step's ``n`` took in *this* model -- the same free variable that
    appears symbolically in the shortcut's own body is what the model
    assigns a concrete value to once combined with the rest of the trace.
    """
    lines: list[str] = []
    total_real_steps = 0
    for step_index, rule in enumerate(trace):
        formulas = summary.formulas_by_rule_id.get(rule.rule_id)
        if formulas is None:
            total_real_steps += 1
            continue
        fresh_n = fresh_rule_vars_by_step[step_index][-1]
        n_value = model.eval(fresh_n, model_completion=True)
        total_real_steps += n_value.as_long()
        formula_str = ", ".join(f"{name}(i) = {expr}" for name, expr in formulas)
        lines.append(
            f"  step {step_index}: rule r{rule.rule_id} (from r{rule.original_rule_id}) "
            f"applied n={n_value} times -- {formula_str}"
        )
    header = (
        f"Witness: {len(trace)} trace step(s) represent N = {total_real_steps} "
        "real transition(s)"
    )
    if not lines:
        return header + " (no accelerated steps used)"
    return "\n".join([header, *lines])
