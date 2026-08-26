"""Forward reachability fixpoint computation via quantifier elimination.

A third, independent strategy alongside SeedMiner/Houdini (guess syntactic
candidates, validate by SMT induction checks) and PhaseFit (guess candidates
from per-branch closed-form analysis). This one doesn't guess at all: it
directly computes the set of reachable states of each relation by symbolic
forward image iteration, using Z3's QE tactic to eliminate the existentially
quantified predecessor state at each step, and keeps going until either

  * the image stops growing for every relation -- the current formula for
    each relation is then, by construction, exactly its set of reachable
    states, which is trivially an inductive invariant (nothing new is ever
    reachable from it). If no query rule is satisfiable under it, the
    program is SAFE, and provably so -- not a guess that survived
    validation, but the literal reachable-state set.
  * a query rule's bad condition becomes satisfiable under the current
    (already fully sound, since every image step is an exact forward step)
    reachable-set formula -- the program is UNSAFE, with a genuine
    counterexample, not a possible one.
  * neither happens within the iteration budget -- UNKNOWN.

That third case is the common one for genuinely unbounded loops (e.g. a
plain counter with no upper bound): the exact reachable set keeps growing
forever and this module has no way to jump ahead to it. To help with that,
`run()` also advances a second, *generalized* track in parallel: it starts
identical to the exact one, but instead of always union-ing in the raw
image, once a variable's per-relation interval bound has moved for two
consecutive rounds (see `widening_delay`) it is widened -- extrapolated all
the way to +/-infinity in one step, rather than tracked incrementally. This
is the classic Cousot-Cousot interval widening operator from abstract
interpretation. It only ever *adds* states relative to the exact reachable
set (an interval bound only gets looser, never tighter), so by induction
the generalized track's formula is always a sound over-approximation of the
true reachable set. That has one direct consequence for how the two tracks
are used:

  * generalized reaching its OWN fixpoint with no query satisfiable against
    it is just as sound a SAFE proof as the exact fixpoint -- a super-set
    with no bad state means the real, smaller set has no bad state either.
  * a query becoming satisfiable against the *generalized* track is NOT
    treated as a counterexample -- it may be a real bug, or it may be an
    artifact of the over-approximation (a state widening added that isn't
    actually reachable). Only a query hit against the *exact* track is
    ever reported as UNSAFE. The exact track keeps running, unmodified, in
    parallel for exactly this reason.

CAUTION -- the exact track's own soundness rests on an assumption that
does not always hold: that Z3's `qe` tactic, when it returns a
leak-free result (see `_qe_exists`), has computed a formula genuinely
equivalent to the existential it was asked to eliminate. This has been
observed to be false for real input: on a benchmark combining integer
`%` (mod) with `If`/ite in the same rule body, `qe` returned a
formula that was satisfied by a concrete state (confirmed via a direct,
tactic-free SAT check) with NO possible predecessor under the actual
rule -- an over-approximation, reproduced even with a 60-second timeout,
so not a timeout artifact. Over-approximation in `reached` cannot cause
a false SAFE (a superset with no query hit still means the true, smaller
set has no query hit either -- the same argument that justifies trusting
the generalized track's own SAFE verdicts above) but it can cause a
false UNSAFE: a query becoming satisfiable purely because of states that
were never actually reachable. Since that is the one direction with real
consequences -- a person could act on a fabricated counterexample --
every exact-track query hit is independently re-checked via
:class:`~pyhorn_bnd.explorer.BoundedExplorer` (a completely separate
code path with no dependency on `qe`, SSA-unrolling the same rules
directly) before it is ever reported as UNSAFE. See
`_confirm_counterexample` and `test_exact_track_rejects_a_qe_over_approximation`.

Interval widening is a non-relational abstraction: it captures each
variable's own range but drops any correlation between variables (e.g.
`x == y` degrades to independent bounds on x and on y). It is also only
applied to relations whose canonical variables are *all* Int/Real sorted --
a relation with any other sort (String, Array, Bool, ...) is left on the
exact track only, unmodified from before generalization was added, since
"infinity" isn't a meaningful bound for those. Both are standard,
acknowledged limitations of interval abstraction, not the kind of thing a
"simple" implementation tries to fix -- a relational domain (octagons,
polyhedra) would recover the dropped correlations at real added complexity.

This module is intentionally "simple" (per the name) otherwise: a direct
Kleene iteration processing every non-fact, non-query rule each round from
a full snapshot of the previous round, with no dependency ordering and no
incremental/interpolation tricks. It only assumes what the rest of this
codebase already assumes about the input: a normalized linear-CHC
:class:`~pyhorn_bnd.horn.HornProgram` (`HornRule.rule_vars` gives exactly
the rule-local variables to existentially eliminate; `HornRule.src_relation`
is at most one relation per rule body, since linear CHC never joins two
relations in one rule).
"""

from __future__ import annotations

import logging
import time
from collections.abc import Mapping
from dataclasses import dataclass, field
from enum import Enum

import z3

from .horn import HornProgram, HornRule
from .seedminer import VariableMap, _canonical_variables

logger = logging.getLogger(__name__)

DEFAULT_MAX_ITERATIONS = 20
DEFAULT_TIMEOUT_MS = 10_000
DEFAULT_OVERALL_TIMEOUT_S = 30.0
DEFAULT_WIDENING_DELAY = 2


class ForwardFixpointStatus(Enum):
    SAFE = "safe"
    UNSAFE = "unsafe"
    UNKNOWN = "unknown"


@dataclass
class ForwardFixpointResult:
    """Outcome of one :func:`run_forward_fixpoint` call."""

    status: ForwardFixpointStatus
    variables: VariableMap
    # Per-relation reachable-set formula, over that relation's own
    # canonical variables (`variables[relation]`). On SAFE, this is the
    # exact set of reachable states (a genuine fixpoint). On UNKNOWN, it's
    # the under-approximation reached before the iteration budget ran out
    # -- still sound (every state in it really is reachable), just not
    # proven complete.
    reached: dict[z3.FuncDeclRef, z3.BoolRef]
    iterations: int
    fixpoint_reached: bool
    violated_rule: HornRule | None = None
    counterexample_model: str | None = None
    message: str = ""
    qe_failures: int = 0
    # Times a candidate counterexample from the exact track failed
    # independent bounded-model-checking confirmation and was rejected
    # rather than reported as UNSAFE -- see the module docstring's
    # CAUTION note. Should be 0 in the overwhelming majority of runs;
    # a nonzero value means `qe` produced at least one over-approximate
    # result along the way, so `reached` may contain unreachable states
    # even though no false UNSAFE escaped this run.
    qe_unsound_rejections: int = 0
    # True when the SAFE verdict came from the generalized (interval-
    # widened) track reaching a fixpoint rather than the exact one. Still
    # a fully sound proof (an over-approximation with no query reachable
    # means the real, smaller reachable set has no query reachable
    # either) -- this just tells the caller `reached` is an
    # over-approximation of the true reachable set on this path, not the
    # exact set. Always False for UNSAFE: a query hit is only ever
    # reported as a genuine counterexample when found against the exact
    # track, never the generalized one (see module docstring).
    generalized: bool = False
    # Populated whenever the generalized (interval-widened) track reached
    # its own global fixpoint at any point during the run, independent of
    # the overall status above -- in particular, this can be non-None even
    # when status is UNKNOWN. It's always a sound over-approximation of
    # the true reachable set (see `generalized` above for why), but on
    # UNKNOWN it specifically means: a query was satisfiable against it,
    # so it wasn't tight enough to prove safety on its own -- see the
    # "generalized fixpoint found but not tight enough" case in
    # docs/forward_fixpoint.md. A caller with an independent way to
    # further constrain a relation (e.g. Houdini-mined candidates) can
    # use this as a starting point: it's already a proven invariant, just
    # possibly too loose.
    generalized_invariant: dict[z3.FuncDeclRef, z3.BoolRef] | None = None


def _instantiate(
    variables: VariableMap,
    relation: z3.FuncDeclRef,
    formula: z3.BoolRef,
    arguments: tuple[z3.ExprRef, ...],
) -> z3.BoolRef:
    """Substitute *relation*'s canonical variables in *formula* with the
    rule-local *arguments* -- turns a formula over `variables[relation]`
    into one over this specific rule's own src_args/dst_args. Safe
    regardless of what *arguments* are (plain variables, literals, or
    compound expressions): the canonical variables are always simple free
    variables that are guaranteed to actually occur in *formula* (it's
    built over exactly `variables[relation]` by construction), so there is
    always something for z3.substitute to find and replace.
    """
    canonical = variables[relation]
    if not canonical:
        return formula
    return z3.substitute(formula, *zip(canonical, arguments, strict=True))


def _has_quantifier(e: z3.ExprRef) -> bool:
    """True if any quantifier (Exists/ForAll) appears anywhere in *e*'s
    AST -- not just whether a *specific* variable remains free. A formula
    can be "quantifier-free with respect to the variables we asked to
    eliminate" while still containing an entirely different, leftover
    quantifier (e.g. an array's own `forall i. a[i] = ...` invariant that
    was already present in a fact rule's body, or one Z3's QE tactic
    introduced/failed to fully resolve): treating that as an ordinary
    quantifier-free formula is both unsound to reuse casually downstream
    and, concretely, breaks z3.Optimize (used for interval bound
    computation), which does not support quantified constraints at all.
    """
    seen: set[int] = set()
    stack = [e]
    while stack:
        expr = stack.pop()
        try:
            eid = expr.get_id()
        except z3.Z3Exception:
            continue
        if eid in seen:
            continue
        seen.add(eid)
        if z3.is_quantifier(expr):
            return True
        if z3.is_app(expr):
            stack.extend(expr.arg(i) for i in range(expr.num_args()))
    return False


def _contains_any_var(e: z3.ExprRef, target_ids: set[int]) -> bool:
    """True if *e*'s AST contains a free variable (an uninterpreted
    0-arity constant, in Z3's terms) whose id is in *target_ids*.

    This exists as a fast, purpose-built replacement for
    ``z3.z3util.get_vars`` (same "is this a variable" semantics --
    ``is_const(f) and f.decl().kind() == Z3_OP_UNINTERPRETED`` -- see
    that function's source), which is a pure-Python utility with no Z3
    timeout hook at all: it deduplicates every AST node by *stringifying*
    it (``vset(..., idfun=str)``), which on a formula that grows every
    round -- the normal case here, since each relation's reachable-set
    formula is a growing union of prior images -- dominates all other
    work by orders of magnitude (measured: 2ms at round 1 growing to 21s
    by round 15 on a small 3-variable benchmark) and is bounded by
    neither ``timeout_ms`` nor the caller's overall deadline, since it
    isn't a tactic or solver call either checks. This walks the DAG once,
    deduped by id (like :func:`_has_quantifier`), and returns as soon as
    a match is found instead of first collecting every variable in the
    formula.
    """
    seen: set[int] = set()
    stack = [e]
    while stack:
        expr = stack.pop()
        try:
            eid = expr.get_id()
        except z3.Z3Exception:
            continue
        if eid in seen:
            continue
        seen.add(eid)
        if (
            z3.is_const(expr)
            and expr.decl().kind() == z3.Z3_OP_UNINTERPRETED
        ):
            if eid in target_ids:
                return True
            continue
        if z3.is_app(expr):
            stack.extend(expr.arg(i) for i in range(expr.num_args()))
    return False


def _qe_exists(
    vars_to_eliminate: tuple[z3.ExprRef, ...],
    body: z3.BoolRef,
    *,
    timeout_ms: int,
) -> z3.BoolRef | None:
    """Existentially eliminate *vars_to_eliminate* from *body* via Z3's QE
    tactic. Returns None if QE fails, times out, or -- checked explicitly,
    since Z3's "qe" tactic is not guaranteed to fully eliminate every
    variable for every theory -- the result still contains *any*
    quantifier at all (not just one binding something in
    *vars_to_eliminate*: a fact rule's own body can already contain an
    unrelated quantifier, e.g. an array initialization invariant, and
    that must be treated the same way -- not passed through as if it
    were an ordinary quantifier-free formula). A caller treating a
    partially-eliminated formula as if it were the true projection would
    silently compute an unsound (wrong, not just incomplete) reachable
    set, so this is a hard correctness requirement here, not just a
    quality check.
    """
    if not vars_to_eliminate:
        simplified = z3.simplify(body)
        return None if _has_quantifier(simplified) else simplified
    try:
        goal = z3.Goal()
        goal.add(z3.Exists(list(vars_to_eliminate), body))
        tactic = z3.TryFor(z3.Tactic("qe"), timeout_ms)
        result = tactic(goal)
    except z3.Z3Exception as exc:
        logger.debug("forward_fixpoint: QE failed: %s", exc)
        return None
    if len(result) == 0:
        return z3.BoolVal(False)
    try:
        exprs = [z3.simplify(g.as_expr()) for g in result]
    except z3.Z3Exception as exc:
        logger.debug("forward_fixpoint: QE post-processing failed: %s", exc)
        return None
    out = exprs[0]
    for e in exprs[1:]:
        out = z3.Or(out, e)
    out = z3.simplify(out)
    if _has_quantifier(out):
        logger.debug(
            "forward_fixpoint: QE left a quantifier in the result -- "
            "treating as failed rather than trusting a possibly-unsound "
            "or Optimize-incompatible partial projection"
        )
        return None
    eliminate_ids = {v.get_id() for v in vars_to_eliminate}
    try:
        leaked = _contains_any_var(out, eliminate_ids)
    except z3.Z3Exception:
        return None
    if leaked:
        logger.debug(
            "forward_fixpoint: QE left a to-be-eliminated variable free "
            "in the result -- treating as failed rather than trusting a "
            "possibly-unsound partial projection"
        )
        return None
    return out


def _entails(a: z3.BoolRef, b: z3.BoolRef, *, timeout_ms: int) -> bool | None:
    """Is `a => b` valid? True/False, or None if the check itself can't
    decide (timeout)."""
    solver = z3.Solver()
    solver.set(timeout=timeout_ms)
    solver.add(a, z3.Not(b))
    result = solver.check()
    if result == z3.unsat:
        return True
    if result == z3.sat:
        return False
    return None


def _is_int_or_real(v: z3.ExprRef) -> bool:
    try:
        return v.sort().kind() in (z3.Z3_INT_SORT, z3.Z3_REAL_SORT)
    except z3.Z3Exception:
        return False


# A per-relation bound map: canonical variable id -> (lo, hi), where each
# side is a concrete Z3 numeral, or None for unbounded in that direction.
BoundMap = dict[int, tuple[z3.ExprRef | None, z3.ExprRef | None]]


def _interval_bounds(
    formula: z3.BoolRef,
    variables: tuple[z3.ExprRef, ...],
    *,
    timeout_ms: int,
) -> BoundMap | None:
    """For each of *variables* (must all be Int/Real sorted), find the
    tightest [lo, hi] interval containing every value it can take under
    *formula*, via one Z3 optimization query per bound per variable.

    Returns None if *formula* is unsatisfiable (the caller should already
    special-case that separately, via z3.BoolVal(False), rather than reach
    here) or if any query can't decide within *timeout_ms* -- generalizing
    from a partially-computed bound would silently either under- or
    over-shoot, so an inconclusive query here means "skip generalization
    this round" for the whole relation, not "assume unbounded" or "assume
    whatever we got".
    """
    bounds: BoundMap = {}
    for v in variables:
        lo: z3.ExprRef | None = None
        hi: z3.ExprRef | None = None
        for maximize in (True, False):
            opt = z3.Optimize()
            opt.set("timeout", timeout_ms)
            opt.add(formula)
            handle = opt.maximize(v) if maximize else opt.minimize(v)
            try:
                result = opt.check()
            except z3.Z3Exception:
                return None
            if result != z3.sat:
                # unsat means *formula* itself is infeasible (shouldn't
                # normally reach here -- see docstring); unknown means a
                # timeout. Either way, no usable bound.
                return None
            val = opt.upper(handle) if maximize else opt.lower(handle)
            concrete = val if (z3.is_int_value(val) or z3.is_rational_value(val)) else None
            if maximize:
                hi = concrete
            else:
                lo = concrete
        bounds[v.get_id()] = (lo, hi)
    return bounds


def _num_le(a: z3.ExprRef, b: z3.ExprRef) -> bool:
    """a <= b for two concrete Z3 numerals (Int or Real)."""
    av = a.as_fraction() if z3.is_rational_value(a) else a.as_long()
    bv = b.as_fraction() if z3.is_rational_value(b) else b.as_long()
    return av <= bv


def _num_eq(a: z3.ExprRef, b: z3.ExprRef) -> bool:
    """a == b for two concrete Z3 numerals (Int or Real)."""
    av = a.as_fraction() if z3.is_rational_value(a) else a.as_long()
    bv = b.as_fraction() if z3.is_rational_value(b) else b.as_long()
    return av == bv


def _widen_bounds(
    old: BoundMap, new: BoundMap, variables: tuple[z3.ExprRef, ...]
) -> BoundMap:
    """The classic Cousot-Cousot interval widening operator: a bound that
    held last round and still holds this round is kept; a bound that has
    moved (which, since `new` only ever accumulates more states than
    `old` via union, only ever means "got looser") is extrapolated all
    the way to unbounded immediately, rather than tracked incrementally.
    This is what turns an unboundedly-growing sequence of ever-looser
    bounds into one that stabilizes in a small, fixed number of rounds --
    at the cost of jumping straight past whatever the tightest true bound
    might have been.
    """
    widened: BoundMap = {}
    for v in variables:
        vid = v.get_id()
        old_lo, old_hi = old.get(vid, (None, None))
        new_lo, new_hi = new.get(vid, (None, None))
        keep_lo = (
            new_lo
            if (old_lo is not None and new_lo is not None and _num_eq(old_lo, new_lo))
            else None
        )
        keep_hi = (
            new_hi
            if (old_hi is not None and new_hi is not None and _num_eq(old_hi, new_hi))
            else None
        )
        widened[vid] = (keep_lo, keep_hi)
    return widened


def _bounds_to_formula(
    variables: tuple[z3.ExprRef, ...], bounds: BoundMap
) -> z3.BoolRef:
    """Build the interval-hull formula And(lo_i <= v_i <= hi_i, ...) from
    a bound map, omitting any side that's unbounded."""
    conjuncts: list[z3.BoolRef] = []
    for v in variables:
        lo, hi = bounds.get(v.get_id(), (None, None))
        if lo is not None:
            conjuncts.append(v >= lo)
        if hi is not None:
            conjuncts.append(v <= hi)
    return z3.And(*conjuncts) if conjuncts else z3.BoolVal(True)


@dataclass
class ForwardFixpoint:
    """Compute (and check) a forward reachability fixpoint for *program*.

    Configuration mirrors the existing drivers in this codebase
    (:class:`~pyhorn_bnd.houdini.MultiHoudini`,
    :class:`~pyhorn_bnd.phasefit.PhaseFit`): construct once, call
    :meth:`run`.
    """

    program: HornProgram
    variables: VariableMap | None = None
    max_iterations: int = DEFAULT_MAX_ITERATIONS
    timeout_ms: int = DEFAULT_TIMEOUT_MS
    overall_timeout_s: float = DEFAULT_OVERALL_TIMEOUT_S
    enable_generalization: bool = True
    # Rounds to let the generalized track grow un-widened before widening
    # kicks in -- lets small, genuinely-bounded systems settle to their
    # exact fixpoint instead of immediately over-generalizing away a bound
    # that was actually about to stabilize on its own.
    widening_delay: int = DEFAULT_WIDENING_DELAY
    # Per-relation formulas that are already known to be true for every
    # reachable state of that relation, established independently of
    # this run (typically a Houdini-certified invariant fed in by an
    # orchestrator alternating between this technique and Houdini -- see
    # ff_houdini.py). Purely additive and always sound to use: it can
    # only tighten a hypothesis or a query check, never loosen one, and
    # it can stand in for a tainted relation's own (possibly-incomplete)
    # computed reachable set, since it doesn't inherit that taint -- it
    # was proven true some other way, not accumulated by this run's own
    # QE steps.
    external_invariants: Mapping[z3.FuncDeclRef, z3.BoolRef] | None = None
    _resolved_variables: VariableMap = field(init=False, repr=False)

    def __post_init__(self) -> None:
        if self.variables is not None:
            self._resolved_variables = self.variables
        else:
            used_names: set[str] = set()
            built: VariableMap = {}
            for relation in self.program.relations:
                canonical, used_names = _canonical_variables(relation, used_names)
                built[relation] = canonical
            self._resolved_variables = built
        self._arithmetic_relations = frozenset(
            rel
            for rel, canonical in self._resolved_variables.items()
            if canonical and all(_is_int_or_real(v) for v in canonical)
        )

    def _remaining_timeout_ms(self, deadline: float) -> int:
        remaining_s = deadline - time.monotonic()
        return max(1, min(self.timeout_ms, int(remaining_s * 1000)))

    def _confirm_counterexample(self, exact_steps: int, deadline: float) -> bool:
        """Independently re-check a candidate exact-track query hit via
        bounded model checking (SSA-unrolling the rules directly, with no
        dependency on `qe`) before it is ever reported as UNSAFE -- see
        the module docstring's CAUTION note. *exact_steps* is the number
        of forward-image rounds the exact track took to reach this hit.

        `BoundedExplorer`'s own notion of trace length counts every rule
        application in the derivation, including the initial fact rule
        and the final query rule -- e.g. one fact application plus two
        step rounds plus the query itself needs `upto=4`, not `upto=2`
        (confirmed via `test_confirm_counterexample_depth_is_sufficient`;
        an earlier version of this check passed `exact_steps` straight
        through as `upto` and wrongly rejected genuine counterexamples
        as a result). `2 * exact_steps + 10` is deliberately generous
        rather than an attempt at the exact minimum: passing too small a
        bound risks exactly that false rejection, while passing too
        large a bound only costs extra search in the (rare, and exactly
        the case this check exists for) event that the hit turns out to
        be spurious -- `explore()` returns as soon as it finds a
        counterexample at any depth, so a generous cap is not a
        generous *cost* when a real one exists at its natural depth.

        True only for a confirmed genuine counterexample. False for
        every other outcome -- including this check's own timeout or an
        inconclusive result -- since the point of this check is to never
        let an unconfirmed hit through; being unable to confirm is
        treated the same as confirming it wasn't real.
        """
        from .explorer import BoundedExplorer, ExplorationStatus

        remaining_ms = max(1, int((deadline - time.monotonic()) * 1000))
        confirmation_timeout_ms = min(self.timeout_ms, remaining_ms)
        upto = 2 * max(exact_steps, 1) + 10
        try:
            result = BoundedExplorer(
                self.program, timeout_ms=confirmation_timeout_ms
            ).explore(start=1, upto=upto)
        except z3.Z3Exception:
            return False
        return result.status is ExplorationStatus.COUNTEREXAMPLE

    def _src_hypothesis(
        self,
        rule: HornRule,
        reached: Mapping[z3.FuncDeclRef, z3.BoolRef],
        *,
        tainted: set[z3.FuncDeclRef],
    ) -> z3.BoolRef | None:
        """The hypothesis for `rule.src_relation`, instantiated over
        `rule.src_args` and (when present) strengthened with
        `self.external_invariants[rule.src_relation]`, ready to conjoin
        into an image computation or a query check.

        `z3.BoolVal(True)` for a fact rule (no `src_relation`).
        `z3.BoolVal(False)` is a real, trustworthy "nothing reaches this
        precondition yet" -- distinct from `None`, which means "we don't
        know, don't compute from this": `src_relation` is tainted and
        there is no external invariant to fall back on. An external
        invariant is unconditionally true by construction (see the field
        docstring), so it doesn't inherit taint -- it can stand in for a
        tainted relation's own incomplete `reached` value entirely,
        rather than blocking the computation the way a bare taint would.
        """
        if rule.src_relation is None:
            return z3.BoolVal(True)
        external = None
        if self.external_invariants is not None:
            external = self.external_invariants.get(rule.src_relation)
        external_instantiated = (
            None
            if external is None
            else _instantiate(
                self._resolved_variables, rule.src_relation, external, rule.src_args
            )
        )
        if rule.src_relation in tainted:
            return external_instantiated
        hypothesis = reached.get(rule.src_relation)
        if hypothesis is None or z3.is_false(hypothesis):
            return z3.BoolVal(False)
        instantiated = _instantiate(
            self._resolved_variables, rule.src_relation, hypothesis, rule.src_args
        )
        if external_instantiated is not None:
            instantiated = z3.And(instantiated, external_instantiated)
        return instantiated

    def _image_of_rule(
        self,
        rule: HornRule,
        reached: Mapping[z3.FuncDeclRef, z3.BoolRef],
        *,
        tainted: set[z3.FuncDeclRef],
        deadline: float,
    ) -> z3.BoolRef | None:
        """Exact forward image of *rule* given the current *reached* sets,
        expressed over `rule.dst_relation`'s canonical variables. None if
        QE couldn't compute it, or if `rule.src_relation` is *tainted*
        with no `external_invariants` entry to fall back on (its own
        `reached` value is known to be incomplete because some earlier
        QE call failed for it -- see `run()`'s docstring note on taint
        propagation). Either way, the caller must treat this round's
        progress for this rule as unknown, never as "nothing new": a
        tainted hypothesis's current formula could be missing real
        states, so a False/empty result computed from it is not evidence
        of unreachability.
        """
        src_hypothesis = self._src_hypothesis(rule, reached, tainted=tainted)
        if src_hypothesis is None:
            return None
        parts = [rule.body]
        if rule.src_relation is not None:
            if z3.is_false(src_hypothesis):
                # Nothing reaches this rule's precondition yet -- no
                # contribution this round (this is exact, not a guess:
                # if src_relation truly has no reachable states so far,
                # this rule cannot fire yet either). Only trustworthy
                # because _src_hypothesis already accounts for taint and
                # external_invariants -- a False here really does mean
                # "computed (or externally known), and empty".
                return z3.BoolVal(False)
            parts.append(src_hypothesis)
        # Tie each of this relation's canonical variables to this rule's
        # own dst_args via equality, rather than trying to substitute
        # dst_args for the canonical variables after projecting onto
        # dst_args. dst_args is not always a plain variable that can be
        # found and replaced syntactically -- a fact rule's dst_args can
        # be a literal constant (e.g. dst_args == ("MI",) for `inv("MI")`
        # with no rule-local variables at all), and substitution silently
        # does nothing when there's no matching subterm to replace,
        # leaving the canonical variables totally unconstrained. Asserting
        # the equality and eliminating dst_args through QE alongside every
        # other rule-local variable works uniformly for a variable, a
        # literal, or any compound expression. Confirmed via
        # test_forward_fixpoint_handles_literal_fact_dst_args (this is
        # exactly what a MU-puzzle-style `(rule (=> (and ...) (inv "MI")))`
        # fact rule looks like after normalization).
        canonical_dst = self._resolved_variables[rule.dst_relation]
        if canonical_dst:
            parts.append(
                z3.And(
                    *(
                        c == a
                        for c, a in zip(canonical_dst, rule.dst_args, strict=True)
                    )
                )
            )
        full = z3.simplify(z3.And(*parts)) if len(parts) > 1 else parts[0]
        if z3.is_false(full):
            return z3.BoolVal(False)
        return _qe_exists(
            rule.rule_vars, full, timeout_ms=self._remaining_timeout_ms(deadline)
        )

    def _check_query(
        self,
        rule: HornRule,
        reached: Mapping[z3.FuncDeclRef, z3.BoolRef],
        *,
        tainted: set[z3.FuncDeclRef],
        deadline: float,
    ) -> z3.ModelRef | None | bool:
        """Is *rule* (a query rule) violated under the current *reached*
        sets? Returns a model if so (genuine counterexample), False if
        definitely not, or None if the check couldn't decide -- including
        when `rule.src_relation` is tainted with no `external_invariants`
        entry to fall back on, since a "definitely not" computed from a
        known-incomplete hypothesis isn't trustworthy: the real
        (untainted) reachable set could include states this one's
        missing, some of which might violate the query. Undecided here
        must never be silently treated as "safe from this query".
        """
        src_hypothesis = self._src_hypothesis(rule, reached, tainted=tainted)
        if src_hypothesis is None:
            return None
        if rule.src_relation is not None and z3.is_false(src_hypothesis):
            return False
        solver = z3.Solver()
        solver.set(timeout=self._remaining_timeout_ms(deadline))
        solver.add(rule.body)
        if rule.src_relation is not None:
            solver.add(src_hypothesis)
        result = solver.check()
        if result == z3.sat:
            return solver.model()
        if result == z3.unsat:
            return False
        return None

    def _advance_generalized(
        self,
        generalized_reached: Mapping[z3.FuncDeclRef, z3.BoolRef],
        prev_bounds: dict[z3.FuncDeclRef, BoundMap],
        *,
        tainted: set[z3.FuncDeclRef],
        iteration: int,
        deadline: float,
    ) -> tuple[dict[z3.FuncDeclRef, z3.BoolRef], dict[z3.FuncDeclRef, BoundMap], bool]:
        """One round of the generalized track: compute the raw forward
        image using *generalized_reached* itself as the hypothesis (so
        this track evolves from its own, already-over-approximate state,
        independently of the exact track), union it in, then widen the
        per-relation interval bounds of any all-arithmetic relation once
        past `widening_delay` rounds. Returns the new reached map, the
        new bound-map cache (for next round's widening comparison), and
        whether any step failed (QE, bound computation, or a tainted
        hypothesis) -- treated the same as the exact track's
        `any_qe_failure_this_round`: such a round cannot be trusted as
        "no progress", so it never counts towards a generalized fixpoint.
        *tainted* is the same set the exact track uses -- taint is a
        property of a relation's reachability computation, not of which
        track is asking about it, so a relation tainted by either track
        must be treated as tainted by both from then on.
        """
        step_rules = [
            r for r in self.program.rules if not r.is_fact and not r.is_query
        ]
        new_reached = dict(generalized_reached)
        any_failure = False
        for rule in step_rules:
            if time.monotonic() >= deadline:
                any_failure = True
                break
            image = self._image_of_rule(
                rule, generalized_reached, tainted=tainted, deadline=deadline
            )
            if image is None:
                any_failure = True
                tainted.add(rule.dst_relation)
                continue
            prior = new_reached[rule.dst_relation]
            new_reached[rule.dst_relation] = z3.simplify(z3.Or(prior, image))

        new_bounds: dict[z3.FuncDeclRef, BoundMap] = {}
        for relation in self._arithmetic_relations:
            if relation in tainted:
                # Bounds computed from an incomplete formula would be
                # incomplete too, and could make the generalized track
                # falsely look like it has stopped growing.
                any_failure = True
                continue
            canonical = self._resolved_variables[relation]
            formula = new_reached[relation]
            if z3.is_false(formula):
                continue
            bounds = _interval_bounds(
                formula, canonical, timeout_ms=self._remaining_timeout_ms(deadline)
            )
            if bounds is None:
                any_failure = True
                continue
            if iteration > self.widening_delay and relation in prev_bounds:
                bounds = _widen_bounds(prev_bounds[relation], bounds, canonical)
                new_reached[relation] = z3.simplify(
                    _bounds_to_formula(canonical, bounds)
                )
            new_bounds[relation] = bounds
        return new_reached, new_bounds, any_failure

    def run(self) -> ForwardFixpointResult:
        variables = self._resolved_variables
        deadline = time.monotonic() + self.overall_timeout_s
        reached: dict[z3.FuncDeclRef, z3.BoolRef] = {
            rel: z3.BoolVal(False) for rel in self.program.relations
        }
        fact_rules = [r for r in self.program.rules if r.is_fact]
        step_rules = [
            r for r in self.program.rules if not r.is_fact and not r.is_query
        ]
        query_rules = [r for r in self.program.rules if r.is_query]

        qe_failures = 0
        qe_unsound_rejections = 0
        # A relation whose reachable-set formula is known to be
        # incomplete, because some rule contributing to it hit a QE
        # failure it could never recover from within this run (an
        # unresolvable quantifier, a timeout, ...). Once tainted, a
        # relation's current `False`/empty-looking formula must never be
        # read as "provably no reachable states" -- only as "we don't
        # know". Taint propagates automatically: _image_of_rule refuses
        # to compute anything from a tainted hypothesis (returns None),
        # which in turn taints whatever rule.dst_relation that computation
        # was for, and so on transitively through the rest of the run.
        tainted: set[z3.FuncDeclRef] = set()

        # Round 0: seed reachable sets from the fact rules.
        for rule in fact_rules:
            image = self._image_of_rule(
                rule, reached, tainted=tainted, deadline=deadline
            )
            if image is None:
                qe_failures += 1
                tainted.add(rule.dst_relation)
                continue
            prior = reached[rule.dst_relation]
            reached[rule.dst_relation] = z3.simplify(z3.Or(prior, image))

        for rule in query_rules:
            outcome = self._check_query(
                rule, reached, tainted=tainted, deadline=deadline
            )
            if outcome is None:
                continue
            if outcome is not False:
                if self._confirm_counterexample(1, deadline):
                    return ForwardFixpointResult(
                        status=ForwardFixpointStatus.UNSAFE,
                        variables=variables,
                        reached=reached,
                        iterations=0,
                        fixpoint_reached=False,
                        violated_rule=rule,
                        counterexample_model=str(outcome),
                        message=f"{rule.short()} is violated by the initial states",
                        qe_failures=qe_failures,
                        qe_unsound_rejections=qe_unsound_rejections,
                    )
                # See the module docstring's CAUTION note: an
                # unconfirmed hit is never reported as UNSAFE. Taint the
                # source relation involved (if any) -- the QE call that
                # produced this state was over-approximate at least
                # once, so the rest of what it computed for that
                # relation can no longer be trusted as exact either.
                qe_unsound_rejections += 1
                if rule.src_relation is not None:
                    tainted.add(rule.src_relation)
                logger.debug(
                    "forward_fixpoint: rejected an unconfirmed exact-track "
                    "query hit for %s at the initial states -- treating "
                    "as tainted rather than reporting a possibly-spurious "
                    "counterexample",
                    rule.short(),
                )

        # The generalized track starts identical to the seeded exact one.
        # Skipped entirely when there is no all-arithmetic relation to
        # ever widen: with nothing to generalize, this track would just
        # duplicate the exact track's own work, round for round, for zero
        # benefit -- purely wasted QE/Optimize calls, confirmed to matter
        # in practice on array- and string-only programs (see
        # test_generalization_is_skipped_when_nothing_is_arithmetic).
        generalization_active = self.enable_generalization and bool(
            self._arithmetic_relations
        )
        generalized_reached: dict[z3.FuncDeclRef, z3.BoolRef] = dict(reached)
        generalized_bounds: dict[z3.FuncDeclRef, BoundMap] = {}
        # Set once the generalized track reaches its own global fixpoint
        # (every relation's widened formula stops growing simultaneously),
        # regardless of whether a query turns out to be satisfiable
        # against it. Surfaced on every return path below via
        # ForwardFixpointResult.generalized_invariant, since it's a sound
        # over-approximating invariant either way -- see that field's
        # docstring. Once set, the generalized track is known stable and
        # is no longer re-advanced each round (nothing left to gain from
        # recomputing an unchanging formula).
        stable_generalized_reached: dict[z3.FuncDeclRef, z3.BoolRef] | None = None
        if generalization_active:
            for relation in self._arithmetic_relations:
                formula = generalized_reached[relation]
                if z3.is_false(formula):
                    continue
                bounds = _interval_bounds(
                    formula,
                    self._resolved_variables[relation],
                    timeout_ms=self._remaining_timeout_ms(deadline),
                )
                if bounds is not None:
                    generalized_bounds[relation] = bounds

        for iteration in range(1, self.max_iterations + 1):
            if time.monotonic() >= deadline:
                return ForwardFixpointResult(
                    status=ForwardFixpointStatus.UNKNOWN,
                    variables=variables,
                    reached=reached,
                    iterations=iteration - 1,
                    fixpoint_reached=False,
                    message=(
                        f"overall time budget ({self.overall_timeout_s}s) "
                        f"exhausted after {iteration - 1} iteration(s) -- "
                        "formulas may be growing faster than the budget "
                        "allows; this is a naive, non-widening iteration"
                    ),
                    qe_failures=qe_failures,
                    qe_unsound_rejections=qe_unsound_rejections,
                    generalized_invariant=stable_generalized_reached,
                )
            new_reached = dict(reached)
            any_qe_failure_this_round = False
            for rule in step_rules:
                if time.monotonic() >= deadline:
                    any_qe_failure_this_round = True
                    break
                image = self._image_of_rule(
                    rule, reached, tainted=tainted, deadline=deadline
                )
                if image is None:
                    qe_failures += 1
                    any_qe_failure_this_round = True
                    tainted.add(rule.dst_relation)
                    continue
                prior = new_reached[rule.dst_relation]
                new_reached[rule.dst_relation] = z3.simplify(z3.Or(prior, image))

            for rule in query_rules:
                outcome = self._check_query(
                    rule, new_reached, tainted=tainted, deadline=deadline
                )
                if outcome is None:
                    continue
                if outcome is not False:
                    if self._confirm_counterexample(iteration, deadline):
                        return ForwardFixpointResult(
                            status=ForwardFixpointStatus.UNSAFE,
                            variables=variables,
                            reached=new_reached,
                            iterations=iteration,
                            fixpoint_reached=False,
                            violated_rule=rule,
                            counterexample_model=str(outcome),
                            message=(
                                f"{rule.short()} is violated after {iteration} "
                                "forward step(s)"
                            ),
                            qe_failures=qe_failures,
                            qe_unsound_rejections=qe_unsound_rejections,
                            generalized_invariant=stable_generalized_reached,
                        )
                    # See the module docstring's CAUTION note: an
                    # unconfirmed hit is never reported as UNSAFE. Taint
                    # the source relation involved (if any) and the rest
                    # of this round's QE-derived states along with it --
                    # the QE call that produced this state was
                    # over-approximate at least once, so nothing derived
                    # from it this round can be trusted as exact either.
                    qe_unsound_rejections += 1
                    any_qe_failure_this_round = True
                    if rule.src_relation is not None:
                        tainted.add(rule.src_relation)
                    logger.debug(
                        "forward_fixpoint: rejected an unconfirmed "
                        "exact-track query hit for %s at iteration %d -- "
                        "treating as tainted rather than reporting a "
                        "possibly-spurious counterexample",
                        rule.short(), iteration,
                    )

            # Inductiveness check: did any relation actually gain new
            # states this round? old => new always holds by construction
            # (new is old-or-something); if new => old also holds for
            # every relation, nothing escaped the old set, so the old set
            # was already closed under every rule -- a fixpoint, and by
            # construction an exact, inductive description of what's
            # reachable.
            all_unchanged = True
            any_undecided = False
            for relation in self.program.relations:
                old, new = reached[relation], new_reached[relation]
                still_contained = _entails(
                    new, old, timeout_ms=self._remaining_timeout_ms(deadline)
                )
                if still_contained is None:
                    any_undecided = True
                    all_unchanged = False
                elif not still_contained:
                    all_unchanged = False

            reached = new_reached
            if all_unchanged and not any_qe_failure_this_round:
                return ForwardFixpointResult(
                    status=ForwardFixpointStatus.SAFE,
                    variables=variables,
                    reached=reached,
                    iterations=iteration,
                    fixpoint_reached=True,
                    message=(
                        f"reached a forward-reachability fixpoint after "
                        f"{iteration} iteration(s); no query is reachable"
                    ),
                    qe_failures=qe_failures,
                    qe_unsound_rejections=qe_unsound_rejections,
                    generalized_invariant=stable_generalized_reached,
                )
            if any_undecided:
                logger.debug(
                    "forward_fixpoint: containment check undecided at "
                    "iteration %d", iteration
                )

            # The exact track didn't converge this round -- try advancing
            # the generalized (widened) track instead, unless it already
            # reached its own stable fixpoint earlier (nothing left to
            # gain from recomputing an unchanging formula each round). It
            # may reach its own fixpoint far sooner than the exact one
            # ever would for a genuinely unbounded-but-safe loop.
            if (
                generalization_active
                and stable_generalized_reached is None
                and time.monotonic() < deadline
            ):
                new_generalized, new_bounds, gen_failure = self._advance_generalized(
                    generalized_reached,
                    generalized_bounds,
                    tainted=tainted,
                    iteration=iteration,
                    deadline=deadline,
                )
                gen_unchanged = True
                gen_undecided = False
                for relation in self.program.relations:
                    old_g = generalized_reached[relation]
                    new_g = new_generalized[relation]
                    still_contained = _entails(
                        new_g, old_g, timeout_ms=self._remaining_timeout_ms(deadline)
                    )
                    if still_contained is None:
                        gen_undecided = True
                        gen_unchanged = False
                    elif not still_contained:
                        gen_unchanged = False
                generalized_reached = new_generalized
                generalized_bounds = new_bounds
                if gen_unchanged and not gen_failure and not gen_undecided:
                    # Generalized fixpoint reached: a sound
                    # over-approximation that has stopped growing. Keep it
                    # regardless of what the query check below finds --
                    # see ForwardFixpointResult.generalized_invariant.
                    stable_generalized_reached = dict(generalized_reached)
                    # Check queries against it -- see module docstring
                    # for why a hit here is never itself reported as
                    # UNSAFE.
                    any_query_hit = False
                    for rule in query_rules:
                        outcome = self._check_query(
                            rule, generalized_reached, tainted=tainted, deadline=deadline
                        )
                        if outcome is None:
                            any_query_hit = True  # undecided -- can't confirm SAFE
                            break
                        if outcome is not False:
                            any_query_hit = True
                            break
                    if not any_query_hit:
                        return ForwardFixpointResult(
                            status=ForwardFixpointStatus.SAFE,
                            variables=variables,
                            reached=generalized_reached,
                            iterations=iteration,
                            fixpoint_reached=True,
                            generalized=True,
                            message=(
                                "reached a generalized (interval-widened) "
                                f"forward-reachability fixpoint after "
                                f"{iteration} iteration(s); no query is "
                                "reachable in the over-approximation"
                            ),
                            qe_failures=qe_failures,
                            qe_unsound_rejections=qe_unsound_rejections,
                            generalized_invariant=stable_generalized_reached,
                        )

        return ForwardFixpointResult(
            status=ForwardFixpointStatus.UNKNOWN,
            variables=variables,
            reached=reached,
            iterations=self.max_iterations,
            fixpoint_reached=False,
            message=(
                f"no fixpoint within {self.max_iterations} iteration(s) "
                "and no query violated -- bounded, inconclusive"
            ),
            qe_failures=qe_failures,
            qe_unsound_rejections=qe_unsound_rejections,
            generalized_invariant=stable_generalized_reached,
        )


def run_forward_fixpoint(
    program: HornProgram,
    *,
    variables: VariableMap | None = None,
    max_iterations: int = DEFAULT_MAX_ITERATIONS,
    timeout_ms: int = DEFAULT_TIMEOUT_MS,
    overall_timeout_s: float = DEFAULT_OVERALL_TIMEOUT_S,
    enable_generalization: bool = True,
    widening_delay: int = DEFAULT_WIDENING_DELAY,
    external_invariants: Mapping[z3.FuncDeclRef, z3.BoolRef] | None = None,
) -> ForwardFixpointResult:
    """Convenience wrapper: construct a :class:`ForwardFixpoint` and run it."""
    return ForwardFixpoint(
        program,
        variables=variables,
        max_iterations=max_iterations,
        timeout_ms=timeout_ms,
        overall_timeout_s=overall_timeout_s,
        enable_generalization=enable_generalization,
        widening_delay=widening_delay,
        external_invariants=external_invariants,
    ).run()
