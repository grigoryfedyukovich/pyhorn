"""Multi-predicate Houdini filtering for seed-mined CHC candidates."""

from __future__ import annotations

from collections.abc import Collection, Mapping
from dataclasses import dataclass
from enum import Enum
from typing import TYPE_CHECKING

import z3
from z3.z3util import get_vars

from .cands import merge_candidate_maps
from .horn import HornProgram, HornRule
from .seedminer import (
    DEFAULT_MAX_EQUALITY_SUBSTITUTIONS_PER_RELATION,
    DEFAULT_MAX_MUTATION_TERMS_PER_RELATION,
    CandidateMap,
    MutationResult,
    SeedMiner,
    SeedMiningResult,
    VariableMap,
    mutate_candidates,
)

if TYPE_CHECKING:
    from .trace_miner import TraceMiningResult


class HoudiniStatus(Enum):
    SUCCESS = "success"
    UNKNOWN = "unknown"


# Adaptive scalar mutation is intentionally wider than the default trace
# mutation pass, but still bounded.  The previous unbounded retry recovered
# useful scalar proofs but could recreate the same quadratic/substitution
# explosion that the default caps were introduced to prevent.
_ADAPTIVE_SCALAR_MUTATION_TERMS = 128
_ADAPTIVE_SCALAR_MUTATION_SUBSTITUTIONS = 4096
_ADAPTIVE_SCALAR_MUTATION_MAX_INPUT_CANDIDATES = 1024


def _scalar_arithmetic_candidate_map(candidates: CandidateMap) -> CandidateMap:
    """Return candidate relations whose arguments are only Int/Real.

    The adaptive mutation fallback deliberately targets scalar arithmetic:
    that is where the FreqHorn regressions from the trace-mutation cap were
    observed, while large array relations paid most of the mutation cost and
    produced no additional proofs.  Keeping this filter relation-based avoids
    inspecting/serializing every candidate formula.
    """
    out: dict[z3.FuncDeclRef, tuple[z3.BoolRef, ...]] = {}
    for relation, relation_candidates in candidates.items():
        if not relation_candidates:
            continue
        try:
            if relation.arity() == 0:
                continue
            if not all(
                relation.domain(i).kind() in (z3.Z3_INT_SORT, z3.Z3_REAL_SORT)
                for i in range(relation.arity())
            ):
                continue
        except z3.Z3Exception:
            continue
        out[relation] = tuple(relation_candidates)
    return out


def _large_array_relations_removed(
    candidates: CandidateMap, *, threshold: int = 64
) -> CandidateMap:
    """Drop only *large* array-typed relations from generic mutation.

    Small array pools retain the existing mutation behavior (important for
    focused array-equality examples).  Trace-mined array pools above the
    threshold are skipped because pairwise/substitution mutation over them was
    responsible for most one-minute benchmark timeouts without adding a single
    proof in the measured FreqHorn suite.
    """
    out: dict[z3.FuncDeclRef, tuple[z3.BoolRef, ...]] = {}
    for relation, relation_candidates in candidates.items():
        items = tuple(relation_candidates)
        if not items:
            continue
        try:
            has_array = any(
                relation.domain(i).kind() == z3.Z3_ARRAY_SORT
                for i in range(relation.arity())
            )
        except z3.Z3Exception:
            has_array = False
        if has_array and len(items) > threshold:
            continue
        out[relation] = items
    return out


@dataclass(frozen=True)
class HoudiniFailure:
    rule_id: int
    rule: str
    reason: str
    model: str | None = None


@dataclass(frozen=True)
class RemovedCandidate:
    """One candidate dropped during Houdini filtering, with its counterexample.

    Captured at the moment a live induction check finds a concrete model
    that falsifies the candidate (a "counterexample to induction", CTI):
    a transition of ``rule`` from ``pre_state`` to ``post_state`` under
    which ``candidate`` does not hold. ``pre_state``/``post_state`` express
    the witness as ``canonical_var = value`` assignments evaluated from the
    countermodel; ``pre_state`` is ``None`` for fact rules, which have no
    source predicate to evaluate. ``full_model`` is the raw ``str(model)``
    for anyone who needs the complete assignment, e.g. over array or
    uninterpreted-sort variables that ``pre_state``/``post_state`` don't
    otherwise surface.

    ``pre_state``/``pre_values`` are one *witness* model, not necessarily a
    faithful representation of what actually makes the candidate
    non-inductive: any variable the active candidate set does not constrain
    (e.g. a loop counter no retained candidate mentions) gets some
    arbitrary, solver-chosen value, which can differ across otherwise
    equivalent runs. ``candidate_validation.py`` therefore does not validate
    this witness at all -- it validates ``candidate_expr`` itself (does some
    real, bounded execution of the program falsify it?), existentially
    quantifying over every variable except the candidate's own rather than
    pinning any of them to values this model happened to report.
    """

    relation: str
    candidate: str  # s-expression of the dropped formula
    rule_id: int
    rule: str  # rule.short()
    pre_state: str | None  # "var = val, ..." for source relation; None for facts
    post_state: str  # "var = val, ..." for destination relation
    full_model: str  # complete Z3 model string
    pre_relation: z3.FuncDeclRef | None = None  # rule.src_relation; None for facts
    # Concrete countermodel values for pre_relation's canonical variables, in
    # canonical order (parallel to pre_state's content, but as real z3
    # expressions rather than formatted text). Display/debugging use only --
    # see the class docstring for why candidate validation does not use
    # these.
    pre_values: tuple[z3.ExprRef, ...] | None = None
    # The dropped formula as an actual z3 expression (not just its sexpr
    # text in `candidate`), over `relation`'s own canonical variables. What
    # candidate_validation.py actually checks.
    candidate_expr: z3.BoolRef | None = None


@dataclass(frozen=True)
class HoudiniStatistics:
    iterations: int
    solver_contexts: int
    solver_checks: int
    candidates_initial: int
    candidates_removed: int
    candidates_remaining: int
    countermodels: int
    unknown_checks: int
    certification_checks: int


@dataclass(frozen=True)
class HoudiniResult:
    status: HoudiniStatus
    variables: VariableMap
    candidates: CandidateMap
    seed_result: SeedMiningResult | None
    statistics: HoudiniStatistics
    failures: tuple[HoudiniFailure, ...]
    removed_candidates: tuple[RemovedCandidate, ...]
    # Populated only by run_trace_houdini() when mutate=True; None otherwise
    # (plain run_seed_houdini() and the CLI's own --seed-houdini/--cands/
    # --mut flow report mutation stats separately, since they build the
    # candidate set themselves rather than through a run_*() convenience
    # function).
    mutation_result: MutationResult | None = None
    # Populated only by run_trace_houdini(); None for plain run_seed_houdini()
    # or CLI --cands runs. Kept separate from removed_candidates (which
    # applies to whichever candidate set MultiHoudini actually filtered)
    # since it describes the trace-sampling stage itself, not a filtering
    # outcome.
    trace_result: TraceMiningResult | None = None
    # Full proposal pool used by the richest staged attempt.  MultiHoudini's
    # ``candidates`` field contains only survivors; FF-Houdini needs the full
    # pool so candidates rejected in one round can become useful after a
    # forward-fixpoint handoff.  Plain run_seed_houdini leaves this as None.
    candidate_pool: CandidateMap | None = None
    # Human/debug label for the stage whose result is returned.
    stage: str | None = None

    @property
    def success(self) -> bool:
        return self.status is HoudiniStatus.SUCCESS


@dataclass
class _RuleContext:
    rule: HornRule
    solver: z3.Solver
    source_guards: tuple[z3.BoolRef, ...]
    source_keys: tuple[str, ...]
    destination_formulas: dict[str, z3.BoolRef]


@dataclass(frozen=True)
class _SolverOutcome:
    result: z3.CheckSatResult
    model: z3.ModelRef | None
    reason_unknown: str | None = None


class MultiHoudini:
    """Incrementally remove candidates refuted by CHC countermodels.

    One persistent filtering solver is built for each relevant non-query CHC.
    Source candidates are asserted behind assumption literals, so removing a
    candidate only changes the assumptions used by later checks.  A violating
    model is asked to falsify at least one active destination candidate; all
    candidates falsified by that model are removed together.  Every original
    CHC is then certified with a fresh solver before ``Success`` is returned.
    """

    def __init__(
        self,
        program: HornProgram,
        variables: VariableMap,
        *,
        timeout_ms: int = 1_000,
        random_seed: int | None = None,
        candidate_kinds: Mapping[str, str] | None = None,
    ):
        if timeout_ms < 0:
            raise ValueError("timeout_ms must be non-negative")
        self.program = program
        self.variables = variables
        self.timeout_ms = timeout_ms
        self.random_seed = random_seed
        # Optional sexpr → TraceMiner kind label (e.g. string-0-count-I-mod-3-in-1-2).
        # Used to discharge hard regex induction by integer arithmetic.
        self.candidate_kinds = dict(candidate_kinds or {})
        # Regex classification is structural but still repeated frequently across
        # filtering/certification. Candidate keys are canonical sexprs, so cache
        # one classification per candidate for the lifetime of this run.
        self._regex_candidate_cache: dict[str, bool] = {}

    def _candidate_is_regex(self, key: str, formula: z3.BoolRef) -> bool:
        cached = self._regex_candidate_cache.get(key)
        if cached is None:
            cached = _is_regex_candidate(key, formula)
            self._regex_candidate_cache[key] = cached
        return cached

    def run(
        self,
        candidates: Mapping[z3.FuncDeclRef, Collection[z3.BoolRef]],
        *,
        seed_result: SeedMiningResult | None = None,
    ) -> HoudiniResult:
        self._validate_candidate_sets(candidates)
        active: dict[z3.FuncDeclRef, dict[str, z3.BoolRef]] = {
            relation: dict(
                sorted(
                    ((candidate.sexpr(), candidate) for candidate in items),
                    key=lambda entry: entry[0],
                )
            )
            for relation, items in candidates.items()
        }
        for relation in self.variables:
            active.setdefault(relation, {})

        # Filtering contexts are useful only for non-query rules whose
        # destination predicate has at least one candidate.  Query clauses are
        # checked once by the independent final certification pass, and rules
        # with destination invariant ``true`` need no Houdini context.
        contexts = [
            self._build_context(rule, active)
            for rule in self.program.rules
            if not rule.is_query and active.get(rule.dst_relation)
        ]
        solver_checks = 0
        certification_checks = 0
        countermodels = 0
        unknown_checks = 0
        candidates_initial = sum(len(items) for items in active.values())
        removed = 0
        iterations = 0
        failures: list[HoudiniFailure] = []
        removed_candidates: list[RemovedCandidate] = []

        while True:
            iterations += 1
            changed = False
            for context in contexts:
                rule = context.rule
                if rule.is_query:
                    continue
                destination = active.get(rule.dst_relation, {})
                if not destination:
                    continue

                outcome = self._check_transition(context, active, destination)
                solver_checks += 1
                if outcome.result == z3.unknown:
                    # Combined check mixed easy refutable candidates (e.g.
                    # length bounds) with hard regex induction. Probe each
                    # destination candidate alone: drop those with a concrete
                    # SAT countermodel; only report unknown if nothing is
                    # refuted and at least one individual check is unknown.
                    bad, extra_checks, probe_unknown = (
                        self._probe_refuted_destination_candidates(
                            context, active, destination
                        )
                    )
                    solver_checks += extra_checks
                    if bad:
                        countermodels += 1
                        for key in bad:
                            if key in destination:
                                if outcome.model is not None:
                                    removed_candidates.append(
                                        self._make_removed_candidate(
                                            rule,
                                            key,
                                            destination[key],
                                            outcome.model,
                                        )
                                    )
                                else:
                                    removed_candidates.append(
                                        RemovedCandidate(
                                            relation=str(
                                                rule.dst_relation.name()
                                            ),
                                            candidate=key,
                                            rule_id=rule.rule_id,
                                            rule=rule.short(),
                                            pre_state=None,
                                            post_state="(individual probe)",
                                            full_model="",
                                            pre_relation=None,
                                            pre_values=None,
                                            candidate_expr=destination[key],
                                        )
                                    )
                                del destination[key]
                                removed += 1
                                changed = True
                        continue
                    if probe_unknown is None:
                        # Every individual obligation discharged (Z3 unsat
                        # or arithmetic count-modulo preservation).
                        continue
                    unknown_checks += 1
                    failures.append(
                        HoudiniFailure(
                            rule_id=rule.rule_id,
                            rule=rule.short(),
                            reason=(
                                probe_unknown
                                or outcome.reason_unknown
                                or "Z3 returned unknown"
                            ),
                        )
                    )
                    return self._result(
                        HoudiniStatus.UNKNOWN,
                        active,
                        seed_result,
                        iterations,
                        len(contexts),
                        solver_checks,
                        candidates_initial,
                        removed,
                        countermodels,
                        unknown_checks,
                        certification_checks,
                        failures,
                        removed_candidates,
                    )
                if outcome.result == z3.unsat:
                    # Still probe regex destinations: they were excluded from
                    # the combined check, so non-inductive alphabet/leading
                    # patterns would otherwise survive until certification.
                    bad_rx, extra_rx, _ = (
                        self._probe_refuted_destination_candidates(
                            context, active, destination
                        )
                    )
                    solver_checks += extra_rx
                    for key in bad_rx:
                        if key in destination and self._candidate_is_regex(
                            key, destination[key]
                        ):
                            removed_candidates.append(
                                RemovedCandidate(
                                    relation=str(rule.dst_relation.name()),
                                    candidate=key,
                                    rule_id=rule.rule_id,
                                    rule=rule.short(),
                                    pre_state=None,
                                    post_state="(regex probe)",
                                    full_model="",
                                    pre_relation=None,
                                    pre_values=None,
                                    candidate_expr=destination[key],
                                )
                            )
                            del destination[key]
                            removed += 1
                            changed = True
                    continue

                if outcome.model is None:
                    raise RuntimeError("SAT Houdini check returned no model")
                model = outcome.model
                countermodels += 1

                def _model_refutes(key: str, formula: z3.BoolRef) -> bool:
                    # Combined check only asserts non-regex destination
                    # violations. A model that falsifies a regex candidate
                    # does so without assuming that regex on the source, so
                    # it is not a valid CTI for that candidate.
                    if self._candidate_is_regex(key, formula):
                        return False
                    kind = self.candidate_kinds.get(key, "")
                    if _arithmetic_count_modulo_preserved(context.rule, kind) is True:
                        return False
                    return z3.is_false(
                        model.eval(formula, model_completion=True)
                    )

                bad = [
                    key
                    for key, formula in context.destination_formulas.items()
                    if key in destination and _model_refutes(key, formula)
                ]
                if not bad:
                    # The asserted disjunction guarantees at least one false
                    # destination formula.  Retain a defensive fallback for
                    # unusual model-evaluation behavior.
                    bad = [
                        key
                        for key, formula in context.destination_formulas.items()
                        if key in destination
                        and _arithmetic_count_modulo_preserved(
                            context.rule, self.candidate_kinds.get(key, "")
                        )
                        is not True
                        and z3.is_true(
                            model.eval(z3.Not(formula), model_completion=True)
                        )
                    ]
                if not bad:
                    # Quantified formulas are not always assigned a concrete
                    # Boolean value by ``model.eval`` even though the combined
                    # violation disjunction is SAT.  Fall back to checking each
                    # active destination candidate separately, as the original
                    # MultiHoudini implementation did after model-based
                    # weakening.
                    bad, extra_checks, probe_unknown = (
                        self._probe_refuted_destination_candidates(
                            context, active, destination
                        )
                    )
                    solver_checks += extra_checks
                    if probe_unknown is not None and not bad:
                        unknown_checks += 1
                        failures.append(
                            HoudiniFailure(
                                rule_id=rule.rule_id,
                                rule=rule.short(),
                                reason=probe_unknown,
                                model=str(model),
                            )
                        )
                        return self._result(
                            HoudiniStatus.UNKNOWN,
                            active,
                            seed_result,
                            iterations,
                            len(contexts),
                            solver_checks,
                            candidates_initial,
                            removed,
                            countermodels,
                            unknown_checks,
                            certification_checks,
                            failures,
                            removed_candidates,
                        )
                if not bad:
                    # A combined disjunction was SAT, but neither model
                    # evaluation nor individual probes identified a refuted
                    # candidate.  This should be unreachable for a sound SMT
                    # solver, but report conservatively instead of turning a
                    # difficult quantified benchmark into an internal error.
                    unknown_checks += 1
                    failures.append(
                        HoudiniFailure(
                            rule_id=rule.rule_id,
                            rule=rule.short(),
                            reason=(
                                "SAT destination violation could not be "
                                "attributed to an active candidate"
                            ),
                            model=str(model),
                        )
                    )
                    return self._result(
                        HoudiniStatus.UNKNOWN,
                        active,
                        seed_result,
                        iterations,
                        len(contexts),
                        solver_checks,
                        candidates_initial,
                        removed,
                        countermodels,
                        unknown_checks,
                        certification_checks,
                        failures,
                        removed_candidates,
                    )

                for key in bad:
                    if key in destination:
                        removed_candidates.append(
                            self._make_removed_candidate(
                                rule, key, destination[key], model
                            )
                        )
                        del destination[key]
                        removed += 1
                        changed = True

            if not changed:
                break

        # Certify every original CHC with a newly constructed solver.  This is
        # deliberately independent of the incremental filtering contexts: a
        # leaked push scope, stale guard, or context-construction error cannot
        # cause a false ``Success``.  Query clauses participate only here.
        for rule in self.program.rules:
            outcome, performed = self._certify_fresh(rule, active)
            if performed:
                solver_checks += 1
                certification_checks += 1
            if outcome.result == z3.unsat:
                continue
            if outcome.result == z3.unknown:
                unknown_checks += 1
                reason = outcome.reason_unknown or "Z3 returned unknown"
            else:
                reason = "CHC is not valid under the retained candidates"
            failures.append(
                HoudiniFailure(
                    rule_id=rule.rule_id,
                    rule=rule.short(),
                    reason=reason,
                    model=None if outcome.model is None else str(outcome.model),
                )
            )

        status = HoudiniStatus.SUCCESS if not failures else HoudiniStatus.UNKNOWN
        return self._result(
            status,
            active,
            seed_result,
            iterations,
            len(contexts),
            solver_checks,
            candidates_initial,
            removed,
            countermodels,
            unknown_checks,
            certification_checks,
            failures,
            removed_candidates,
        )

    def _validate_candidate_sets(
        self, candidates: Mapping[z3.FuncDeclRef, Collection[z3.BoolRef]]
    ) -> None:
        for relation, items in candidates.items():
            if relation not in self.variables:
                raise ValueError(
                    f"candidate set provided for unknown/query relation {relation.name()}"
                )
            allowed = self.variables[relation]
            allowed_ids = {variable.get_id() for variable in allowed}
            for candidate in items:
                if not z3.is_bool(candidate):
                    raise ValueError(
                        f"non-Boolean candidate for {relation.name()}: {candidate}"
                    )
                for variable in get_vars(candidate):
                    if variable.get_id() not in allowed_ids:
                        raise ValueError(
                            f"candidate for {relation.name()} contains foreign "
                            f"variable {variable}: {candidate}"
                        )

    def _build_context(
        self,
        rule: HornRule,
        candidates: Mapping[z3.FuncDeclRef, Mapping[str, z3.BoolRef]],
    ) -> _RuleContext:
        solver = z3.Solver()
        solver.set(timeout=self.timeout_ms)
        if self.random_seed is not None:
            solver.set(random_seed=self.random_seed)
        solver.add(rule.body)

        source_guards: list[z3.BoolRef] = []
        source_keys: list[str] = []
        if rule.src_relation is not None and rule.src_relation in self.variables:
            source = candidates.get(rule.src_relation, {})
            for index, (key, candidate) in enumerate(source.items()):
                guard = z3.FreshBool(f"houdini_r{rule.rule_id}_src_{index}")
                instantiated = self._instantiate(
                    rule.src_relation, candidate, rule.src_args
                )
                solver.add(z3.Implies(guard, instantiated))
                source_guards.append(guard)
                source_keys.append(key)

        destination_formulas: dict[str, z3.BoolRef] = {}
        if not rule.is_query and rule.dst_relation in self.variables:
            destination = candidates.get(rule.dst_relation, {})
            destination_formulas = {
                key: self._instantiate(rule.dst_relation, candidate, rule.dst_args)
                for key, candidate in destination.items()
            }

        return _RuleContext(
            rule=rule,
            solver=solver,
            source_guards=tuple(source_guards),
            source_keys=tuple(source_keys),
            destination_formulas=destination_formulas,
        )

    def _active_source_assumptions(
        self,
        context: _RuleContext,
        active: Mapping[z3.FuncDeclRef, Mapping[str, z3.BoolRef]],
    ) -> list[z3.BoolRef]:
        relation = context.rule.src_relation
        if relation is None:
            return []
        active_keys = active.get(relation, {})
        return [
            guard
            for guard, key in zip(
                context.source_guards, context.source_keys, strict=True
            )
            if key in active_keys
        ]

    def _check_transition(
        self,
        context: _RuleContext,
        active: Mapping[z3.FuncDeclRef, Mapping[str, z3.BoolRef]],
        destination: Mapping[str, z3.BoolRef],
    ) -> _SolverOutcome:
        # Combined SMT check only uses non-regex destination candidates.
        # Count-modulo is discharged by arithmetic; other InRe patterns
        # (alphabet, leading-symbol) are checked individually in the probe
        # path so they cannot time out the combined query.
        violated = []
        for key, formula in context.destination_formulas.items():
            if key not in destination:
                continue
            kind = self.candidate_kinds.get(key, "")
            arith = _arithmetic_count_modulo_preserved(context.rule, kind)
            if arith is True:
                continue
            if arith is False:
                # Arithmetically refuted — force a SAT-shaped outcome by
                # leaving a trivial violation; the probe path records it.
                violated.append(z3.BoolVal(True))
                continue
            if self._candidate_is_regex(key, formula):
                continue
            violated.append(z3.Not(formula))
        if not violated:
            return _SolverOutcome(z3.unsat, None)
        # Fresh solver: the persistent context solver retains implication
        # clauses for hard regex candidates (even when their guards are
        # off), which can make simple prefix/length checks time out.
        solver = z3.Solver()
        solver.set(timeout=self.timeout_ms)
        if self.random_seed is not None:
            solver.set(random_seed=self.random_seed)
        solver.add(context.rule.body)
        relation = context.rule.src_relation
        if relation is not None and relation in self.variables:
            active_src = active.get(relation, {})
            for key, cand in active_src.items():
                if self._candidate_is_regex(key, cand):
                    continue
                if _parse_count_modulo_kind(self.candidate_kinds.get(key, "")):
                    continue
                solver.add(
                    self._instantiate(relation, cand, context.rule.src_args)
                )
        solver.add(z3.Or(*violated))
        result = solver.check()
        if result == z3.unknown and self.timeout_ms > 0:
            boost_ms = min(max(self.timeout_ms * 5, 3_000), 15_000)
            if boost_ms > self.timeout_ms:
                solver.set(timeout=boost_ms)
                result = solver.check()
        model = solver.model() if result == z3.sat else None
        reason = solver.reason_unknown() if result == z3.unknown else None
        return _SolverOutcome(result, model, reason)

    def _probe_refuted_destination_candidates(
        self,
        context: _RuleContext,
        active: Mapping[z3.FuncDeclRef, Mapping[str, z3.BoolRef]],
        destination: Mapping[str, z3.BoolRef],
    ) -> tuple[list[str], int, str | None]:
        """Find candidates refuted individually when model evaluation is partial.

        Also used when the combined transition check returns unknown: easy
        candidates (length bounds, etc.) often have concrete CTIs that the
        combined query cannot surface because a sibling regex obligation
        times out. Arithmetic discharge of character-count modulo kinds is
        applied when Z3 returns unknown so MU-style doubling rules can be
        closed without the string solver.
        """

        easy_assumptions = self._easy_source_assumptions(context, active)
        bad: list[str] = []
        checks = 0
        first_unknown: str | None = None
        for key, formula in context.destination_formulas.items():
            if key not in destination:
                continue
            # Prefer integer discharge for count-modulo kinds before SMT.
            kind = self.candidate_kinds.get(key, "")
            arith = _arithmetic_count_modulo_preserved(context.rule, kind)
            if arith is True:
                continue
            if arith is False:
                bad.append(key)
                continue
            context.solver.push()
            try:
                context.solver.add(z3.Not(formula))
                # Exclude count-modulo source assumptions so their regex
                # form does not time out sibling probes (prefix, bounds).
                result = context.solver.check(*easy_assumptions)
                checks += 1
                if result == z3.sat:
                    bad.append(key)
                elif result == z3.unknown and first_unknown is None:
                    first_unknown = (
                        context.solver.reason_unknown()
                        or "Z3 returned unknown"
                    )
            finally:
                context.solver.pop()
        return bad, checks, first_unknown

    def _easy_source_assumptions(
        self,
        context: _RuleContext,
        active: Mapping[z3.FuncDeclRef, Mapping[str, z3.BoolRef]],
    ) -> list[z3.BoolRef]:
        """Source assumptions excluding regex/InRe candidates.

        ``str.in_re`` obligations (alphabet closure, count-modulo, leading
        patterns) are either discharged by arithmetic or are cheap to check
        as destination-only goals; as *source* assumptions they time out
        sibling probes.
        """
        relation = context.rule.src_relation
        if relation is None:
            return []
        active_keys = active.get(relation, {})
        return [
            guard
            for guard, key in zip(
                context.source_guards, context.source_keys, strict=True
            )
            if key in active_keys
            and not self._candidate_is_regex(key, active_keys[key])
        ]

    def _certify_fresh(
        self,
        rule: HornRule,
        active: Mapping[z3.FuncDeclRef, Mapping[str, z3.BoolRef]],
    ) -> tuple[_SolverOutcome, bool]:
        """Validate one final CHC using a solver with no filtering history."""

        if not rule.is_query and not active.get(rule.dst_relation, {}):
            # The destination invariant is ``true``.
            return _SolverOutcome(z3.unsat, None), False

        if not rule.is_query:
            dest = active.get(rule.dst_relation, {})
            # Per-candidate certification: count-modulo via arithmetic, other
            # formulas via a small SMT check that excludes regex sources.
            for key, candidate in dest.items():
                kind = self.candidate_kinds.get(key, "")
                arith = _arithmetic_count_modulo_preserved(rule, kind)
                if arith is True:
                    continue
                if arith is False:
                    return _SolverOutcome(z3.sat, None), True
                solver2 = z3.Solver()
                solver2.set(timeout=min(max(self.timeout_ms, 2_000), 10_000))
                if self.random_seed is not None:
                    solver2.set(random_seed=self.random_seed)
                solver2.add(rule.body)
                if (
                    rule.src_relation is not None
                    and rule.src_relation in self.variables
                ):
                    for src_key, src_cand in active.get(
                        rule.src_relation, {}
                    ).items():
                        if self._candidate_is_regex(src_key, src_cand):
                            continue
                        solver2.add(
                            self._instantiate(
                                rule.src_relation, src_cand, rule.src_args
                            )
                        )
                solver2.add(
                    z3.Not(
                        self._instantiate(
                            rule.dst_relation, candidate, rule.dst_args
                        )
                    )
                )
                r2 = solver2.check()
                if r2 == z3.unsat:
                    continue
                if r2 == z3.sat:
                    return _SolverOutcome(z3.sat, solver2.model()), True
                return (
                    _SolverOutcome(
                        z3.unknown, None, "Z3 returned unknown"
                    ),
                    True,
                )
            return _SolverOutcome(z3.unsat, None), True

        # Query rule: active invariant must exclude the error state.
        solver = z3.Solver()
        solver.set(timeout=self.timeout_ms)
        if self.random_seed is not None:
            solver.set(random_seed=self.random_seed)
        solver.add(rule.body)
        if rule.src_relation is not None and rule.src_relation in self.variables:
            for key, candidate in active.get(rule.src_relation, {}).items():
                # Prefer ground checks: instantiate each candidate.
                solver.add(
                    self._instantiate(rule.src_relation, candidate, rule.src_args)
                )
        result = solver.check()
        if result == z3.unknown and self.timeout_ms > 0:
            boost_ms = min(max(self.timeout_ms * 5, 3_000), 15_000)
            if boost_ms > self.timeout_ms:
                solver.set(timeout=boost_ms)
                result = solver.check()
        # Ground query (e.g. inv("MU")): try each candidate alone on unknown.
        if result == z3.unknown and rule.src_relation is not None:
            ok = True
            for key, candidate in active.get(rule.src_relation, {}).items():
                kind = self.candidate_kinds.get(key, "")
                parsed = _parse_count_modulo_kind(kind)
                if parsed is not None:
                    # Evaluate count-modulo on the concrete bad string if any.
                    char, modulus, residues = parsed
                    # Body is typically (inv s) with s bound in query as const.
                    # Fall through to SMT for safety.
                    ok = False
                    break
                s2 = z3.Solver()
                s2.set(timeout=3_000)
                s2.add(rule.body)
                s2.add(
                    self._instantiate(
                        rule.src_relation, candidate, rule.src_args
                    )
                )
                if s2.check() == z3.sat:
                    ok = False
                    break
            if ok and active.get(rule.src_relation, {}):
                # Re-check query with only non-regex candidates + arithmetic
                # residual: for MU, PrefixOf("M","MU") is true so need modulo.
                pass
        model = solver.model() if result == z3.sat else None
        reason = solver.reason_unknown() if result == z3.unknown else None
        return _SolverOutcome(result, model, reason), True

    def _instantiate(
        self,
        relation: z3.FuncDeclRef,
        candidate: z3.BoolRef,
        arguments: tuple[z3.ExprRef, ...],
    ) -> z3.BoolRef:
        variables = self.variables[relation]
        if len(variables) != len(arguments):
            raise ValueError(
                f"arity mismatch for {relation.name()}: "
                f"{len(variables)} variables and {len(arguments)} arguments"
            )
        if not variables:
            return candidate
        return z3.substitute(candidate, *zip(variables, arguments, strict=True))

    def _format_state(
        self,
        relation: z3.FuncDeclRef,
        args: tuple[z3.ExprRef, ...],
        model: z3.ModelRef,
    ) -> str:
        """Evaluate *args* in *model*, labelled by *relation*'s canonical names.

        *args* are the rule-instance-specific terms passed to *relation* at
        this call site (e.g. ``x + 1``); *model* is the countermodel that
        refuted a destination candidate. Pairing follows the same
        ``zip(canonical, args)`` convention as :meth:`_instantiate`, so the
        printed name always matches the variable :meth:`_instantiate` would
        have substituted it for.
        """
        canonical = self.variables[relation]
        return ", ".join(
            f"{var} = {model.eval(arg, model_completion=True)}"
            for var, arg in zip(canonical, args)
        )

    def _make_removed_candidate(
        self,
        rule: HornRule,
        candidate_key: str,
        candidate_expr: z3.BoolRef,
        model: z3.ModelRef,
    ) -> RemovedCandidate:
        """Build a :class:`RemovedCandidate` witness from the live induction model.

        Called immediately after *model* is found to falsify the candidate
        keyed by *candidate_key* under *rule*, before that candidate is
        dropped from the active set -- so *model* is still the exact
        countermodel that caused the removal, not a later, unrelated one.
        *candidate_expr* is that same candidate's actual z3 expression
        (the dict value *candidate_key* indexes, i.e. ``destination[key]``
        at the call site), preserved for reachability validation; see
        :class:`RemovedCandidate`'s docstring for why the witness model
        itself is not what that validation uses.
        """
        post_state = self._format_state(rule.dst_relation, rule.dst_args, model)
        pre_state: str | None = None
        pre_relation: z3.FuncDeclRef | None = None
        pre_values: tuple[z3.ExprRef, ...] | None = None
        if rule.src_relation is not None and rule.src_relation in self.variables:
            pre_state = self._format_state(rule.src_relation, rule.src_args, model)
            pre_relation = rule.src_relation
            pre_values = tuple(
                model.eval(arg, model_completion=True) for arg in rule.src_args
            )
        return RemovedCandidate(
            relation=str(rule.dst_relation.name()),
            candidate=candidate_key,
            rule_id=rule.rule_id,
            rule=rule.short(),
            pre_state=pre_state,
            post_state=post_state,
            full_model=str(model),
            pre_relation=pre_relation,
            pre_values=pre_values,
            candidate_expr=candidate_expr,
        )

    def _result(
        self,
        status: HoudiniStatus,
        active: Mapping[z3.FuncDeclRef, Mapping[str, z3.BoolRef]],
        seed_result: SeedMiningResult | None,
        iterations: int,
        solver_contexts: int,
        solver_checks: int,
        candidates_initial: int,
        candidates_removed: int,
        countermodels: int,
        unknown_checks: int,
        certification_checks: int,
        failures: list[HoudiniFailure],
        removed_candidates: list[RemovedCandidate],
    ) -> HoudiniResult:
        final_candidates: CandidateMap = {
            relation: tuple(
                expression
                for _, expression in sorted(items.items(), key=lambda entry: entry[0])
            )
            for relation, items in active.items()
        }
        remaining = sum(len(items) for items in final_candidates.values())
        return HoudiniResult(
            status=status,
            variables=self.variables,
            candidates=final_candidates,
            seed_result=seed_result,
            statistics=HoudiniStatistics(
                iterations=iterations,
                solver_contexts=solver_contexts,
                solver_checks=solver_checks,
                candidates_initial=candidates_initial,
                candidates_removed=candidates_removed,
                candidates_remaining=remaining,
                countermodels=countermodels,
                unknown_checks=unknown_checks,
                certification_checks=certification_checks,
            ),
            failures=tuple(failures),
            removed_candidates=tuple(removed_candidates),
        )


def run_seed_houdini(
    program: HornProgram,
    *,
    timeout_ms: int = 1_000,
    random_seed: int | None = None,
    extra_candidates: CandidateMap | None = None,
) -> HoudiniResult:
    """Mine candidates, run MultiHoudini, and validate all CHCs.

    ``extra_candidates``, if given, is merged in alongside the mined
    candidates before filtering -- e.g. a per-relation invariant an
    orchestrator has independently established some other way. It must
    be expressed over the same canonical variables ``SeedMiner``
    allocates for this *program* (i.e.
    ``SeedMiner(program).variables``), or the merge will not line up with
    what MultiHoudini expects for each relation.
    """

    seeds = SeedMiner(program).mine()
    candidates: CandidateMap = seeds.candidates
    if extra_candidates:
        candidates = merge_candidate_maps(candidates, extra_candidates)
    result = MultiHoudini(
        program,
        seeds.variables,
        timeout_ms=timeout_ms,
        random_seed=random_seed,
    ).run(candidates, seed_result=seeds)
    # MultiHoudini can also be used with manually supplied variables.  The
    # convenience pipeline always returns the seed miner's variable map.
    return HoudiniResult(
        status=result.status,
        variables=seeds.variables,
        candidates=result.candidates,
        seed_result=seeds,
        statistics=result.statistics,
        failures=result.failures,
        removed_candidates=result.removed_candidates,
    )


def run_trace_houdini(
    program: HornProgram,
    *,
    trace_depth: int = 8,
    trace_limit: int = 1_000,
    models_per_prefix: int = 2,
    max_samples_per_relation: int = 64,
    max_trace_candidates_per_relation: int = 256,
    timeout_ms: int = 1_000,
    random_seed: int | None = None,
    mutate: bool = False,
    max_mutation_terms_per_relation: int | None = (
        DEFAULT_MAX_MUTATION_TERMS_PER_RELATION
    ),
    max_mutation_substitutions_per_relation: int | None = (
        DEFAULT_MAX_EQUALITY_SUBSTITUTIONS_PER_RELATION
    ),
    extra_candidates: CandidateMap | None = None,
    seed_result: SeedMiningResult | None = None,
    use_phasefit: bool = False,
    use_trace: bool = True,
) -> HoudiniResult:
    """Run one monotone staged invariant-synthesis portfolio.

    The ordering is deliberately *generation monotone*, not merely Houdini
    monotone.  In particular, expensive PhaseFit generation is never executed
    before the cheap Seed-Houdini baseline has had a chance to prove the
    program.  When both PhaseFit and trace mutation are requested, the
    PhaseFit-free trace/mutation portfolio is also tried before mutating the
    richer pool.  This preserves proofs that can otherwise disappear merely
    because a finite mutation budget is consumed by extra PhaseFit terms.

    Stages (when requested) are::

        seed
        seed + caller-supplied extras
        seed/extras + trace
        seed/extra + trace + mutation
        seed/extra + PhaseFit
        seed/extra + PhaseFit + trace
        seed/extra + PhaseFit + trace + mutation

    Any SUCCESS returns immediately.  ``candidate_pool`` on the returned
    :class:`HoudiniResult` records the full proposal pool of the returned (or
    richest attempted) stage so FF-Houdini can reuse it without regenerating
    PhaseFit/trace candidates.
    """

    from .trace_miner import TraceCandidateMiner

    seeds = seed_result if seed_result is not None else SeedMiner(program).mine()
    seed_pool: CandidateMap = seeds.candidates

    def _run(
        pool: CandidateMap,
        *,
        kind_map: Mapping[str, str] | None = None,
    ) -> HoudiniResult:
        return MultiHoudini(
            program,
            seeds.variables,
            timeout_ms=timeout_ms,
            random_seed=random_seed,
            candidate_kinds=kind_map,
        ).run(pool, seed_result=seeds)

    def _pack(
        result: HoudiniResult,
        pool: CandidateMap,
        stage: str,
        *,
        mutation_result: MutationResult | None = None,
        traces: TraceMiningResult | None = None,
    ) -> HoudiniResult:
        return HoudiniResult(
            status=result.status,
            variables=seeds.variables,
            candidates=result.candidates,
            seed_result=seeds,
            statistics=result.statistics,
            failures=result.failures,
            removed_candidates=result.removed_candidates,
            mutation_result=mutation_result,
            trace_result=traces,
            candidate_pool=pool,
            stage=stage,
        )

    def _mutate_and_run(
        pool: CandidateMap,
        *,
        kind_map: Mapping[str, str] | None,
        traces: TraceMiningResult | None,
    ) -> tuple[HoudiniResult, CandidateMap, MutationResult]:
        mutation_input = _large_array_relations_removed(pool)
        mutation_result = mutate_candidates(
            mutation_input,
            max_terms_per_relation=max_mutation_terms_per_relation,
            max_equality_substitutions_per_relation=(
                max_mutation_substitutions_per_relation
            ),
        )
        mutated = merge_candidate_maps(pool, mutation_result.candidates)
        final = _run(mutated, kind_map=kind_map)
        if final.status is HoudiniStatus.SUCCESS:
            return final, mutated, mutation_result

        # A wider scalar retry is deliberately attempted only for default
        # budgets.  Explicit CLI caps are hard user choices and are preserved.
        use_adaptive_scalar_retry = (
            max_mutation_terms_per_relation
            == DEFAULT_MAX_MUTATION_TERMS_PER_RELATION
            and max_mutation_substitutions_per_relation
            == DEFAULT_MAX_EQUALITY_SUBSTITUTIONS_PER_RELATION
        )
        if use_adaptive_scalar_retry:
            scalar_input = _scalar_arithmetic_candidate_map(pool)
            scalar_input_size = sum(len(items) for items in scalar_input.values())
            if (
                scalar_input
                and scalar_input_size
                <= _ADAPTIVE_SCALAR_MUTATION_MAX_INPUT_CANDIDATES
            ):
                expanded_mutation = mutate_candidates(
                    scalar_input,
                    max_terms_per_relation=_ADAPTIVE_SCALAR_MUTATION_TERMS,
                    max_equality_substitutions_per_relation=(
                        _ADAPTIVE_SCALAR_MUTATION_SUBSTITUTIONS
                    ),
                )
                expanded_pool = merge_candidate_maps(
                    mutated, expanded_mutation.candidates
                )
                if sum(map(len, expanded_pool.values())) > sum(
                    map(len, mutated.values())
                ):
                    expanded = _run(expanded_pool, kind_map=kind_map)
                    # Return the richest attempted pool even on UNKNOWN; FF can
                    # reuse it, and a later PhaseFit-enriched stage can extend it.
                    return expanded, expanded_pool, expanded_mutation
        return final, mutated, mutation_result

    # Stage 0: cheapest complete baseline.  No user extras, trace, mutation,
    # or PhaseFit have been invoked yet.
    baseline = _run(seed_pool)
    if baseline.status is HoudiniStatus.SUCCESS:
        return _pack(baseline, seed_pool, "seed")

    base = seed_pool
    last_result = baseline
    last_pool = seed_pool
    last_stage = "seed"
    if extra_candidates:
        extra_pool = merge_candidate_maps(seed_pool, extra_candidates)
        extra_pass = _run(extra_pool)
        base = extra_pool
        last_result, last_pool, last_stage = extra_pass, extra_pool, "extra"
        if extra_pass.status is HoudiniStatus.SUCCESS:
            return _pack(extra_pass, extra_pool, "extra")
    last_mutation: MutationResult | None = None
    trace_mutated_pool: CandidateMap | None = None

    phasefit_candidates: CandidateMap | None = None
    phasefit_pool = base

    traces: TraceMiningResult | None = None
    kind_map: dict[str, str] = {}
    trace_pool = base
    if use_trace:
        traces = TraceCandidateMiner(
            program,
            seeds.variables,
            max_depth=trace_depth,
            max_prefixes=trace_limit,
            models_per_prefix=models_per_prefix,
            max_samples_per_relation=max_samples_per_relation,
            max_candidates_per_relation=max_trace_candidates_per_relation,
            timeout_ms=timeout_ms,
            random_seed=random_seed,
        ).mine()
        trace_pool = merge_candidate_maps(base, traces.candidates)
        # MultiHoudini currently keys candidates by canonical s-expression.
        # Keep kind metadata aligned with that key until the active-candidate
        # representation itself is migrated away from strings.
        kind_map = {obs.candidate.sexpr(): obs.kind for obs in traces.observations}
        trace_pass = _run(trace_pool, kind_map=kind_map)
        last_result, last_pool, last_stage = trace_pass, trace_pool, "trace"
        if trace_pass.status is HoudiniStatus.SUCCESS:
            return _pack(trace_pass, trace_pool, "trace", traces=traces)

        # Important regression-recovery stage: mutate the PhaseFit-free trace
        # pool first.  Historical exact-iteration proofs depended on these
        # mutations; adding PhaseFit terms ahead of a finite mutation budget
        # can crowd the useful terms out.
        if mutate:
            trace_mut, trace_mut_pool, trace_mutation = _mutate_and_run(
                trace_pool,
                kind_map=kind_map,
                traces=traces,
            )
            trace_mutated_pool = trace_mut_pool
            last_result, last_pool, last_stage, last_mutation = (
                trace_mut,
                trace_mut_pool,
                "trace-mutation",
                trace_mutation,
            )
            if trace_mut.status is HoudiniStatus.SUCCESS:
                return _pack(
                    trace_mut,
                    trace_mut_pool,
                    "trace-mutation",
                    mutation_result=trace_mutation,
                    traces=traces,
                )

    if use_phasefit:
        from .phasefit import run_phasefit

        _pf_results, phasefit_candidates = run_phasefit(
            program, seed_result=seeds
        )
        phasefit_pool = merge_candidate_maps(base, phasefit_candidates)
        if sum(map(len, phasefit_pool.values())) > sum(map(len, base.values())):
            phasefit_pass = _run(phasefit_pool)
            last_result, last_pool, last_stage = (
                phasefit_pass,
                phasefit_pool,
                "phasefit",
            )
            if phasefit_pass.status is HoudiniStatus.SUCCESS:
                return _pack(phasefit_pass, phasefit_pool, "phasefit")

    # If both generators were requested, try their union only *after* each
    # cheaper source has had its own chance.  This preserves combination wins
    # without allowing PhaseFit to starve the trace-only mutation budget.
    combined_pool = phasefit_pool
    if use_trace:
        combined_pool = merge_candidate_maps(
            phasefit_pool, traces.candidates if traces else {}
        )

    if use_phasefit and use_trace:
        combined_pass = _run(combined_pool, kind_map=kind_map)
        last_result, last_pool, last_stage = (
            combined_pass,
            combined_pool,
            "phasefit-trace",
        )
        if combined_pass.status is HoudiniStatus.SUCCESS:
            return _pack(
                combined_pass,
                combined_pool,
                "phasefit-trace",
                traces=traces,
            )

        # Preserve trace-derived mutations when adding PhaseFit candidates.
        # Re-generating mutations over the richer pool can choose a different
        # bounded subset, so explicitly try the union before asking mutation
        # to spend another finite budget.
        if mutate and trace_mutated_pool is not None:
            combined_with_trace_mutation = merge_candidate_maps(
                phasefit_pool, trace_mutated_pool
            )
            carried = _run(combined_with_trace_mutation, kind_map=kind_map)
            last_result, last_pool, last_stage = (
                carried,
                combined_with_trace_mutation,
                "phasefit-trace-carried-mutation",
            )
            if carried.status is HoudiniStatus.SUCCESS:
                return _pack(
                    carried,
                    combined_with_trace_mutation,
                    "phasefit-trace-carried-mutation",
                    mutation_result=last_mutation,
                    traces=traces,
                )

    if mutate and (use_phasefit or (not use_trace)):
        # For PhaseFit+Trace this is the final richer mutation attempt.  With
        # PhaseFit but no trace it is the natural PhaseFit mutation stage.
        mutation_base = combined_pool if use_trace else phasefit_pool
        if use_trace and trace_mutated_pool is not None:
            mutation_base = merge_candidate_maps(
                mutation_base, trace_mutated_pool
            )
        rich_mut, rich_mut_pool, rich_mutation = _mutate_and_run(
            mutation_base,
            kind_map=kind_map,
            traces=traces,
        )
        last_result, last_pool, last_stage, last_mutation = (
            rich_mut,
            rich_mut_pool,
            "phasefit-trace-mutation" if use_trace else "phasefit-mutation",
            rich_mutation,
        )
        if rich_mut.status is HoudiniStatus.SUCCESS:
            return _pack(
                rich_mut,
                rich_mut_pool,
                last_stage,
                mutation_result=rich_mutation,
                traces=traces,
            )

    return _pack(
        last_result,
        last_pool,
        last_stage,
        mutation_result=last_mutation,
        traces=traces,
    )


def _is_regex_candidate(key: str, formula: z3.BoolRef) -> bool:
    """Return whether *formula* contains a regular-expression membership.

    This intentionally avoids ``formula.sexpr()``.  Serializing a large Z3 AST
    merely to search for ``str.in_re`` showed up as a dominant cost (and could
    be interrupted) in FF-Houdini runs.  The candidate key is already available
    for the common fast path; otherwise walk the AST structurally, including
    quantified bodies.
    """
    if "str.in_re" in key or "InRe" in key:
        return True

    stack: list[z3.ExprRef] = [formula]
    seen: set[int] = set()
    while stack:
        current = stack.pop()
        try:
            ast_id = current.get_id()
        except z3.Z3Exception:
            continue
        if ast_id in seen:
            continue
        seen.add(ast_id)

        try:
            if z3.is_app(current) and current.decl().kind() == z3.Z3_OP_SEQ_IN_RE:
                return True
            if z3.is_quantifier(current):
                stack.append(current.body())
            else:
                stack.extend(current.children())
        except z3.Z3Exception:
            continue
    return False


def _parse_count_modulo_kind(
    kind: str,
) -> tuple[str, int, frozenset[int]] | None:
    """Parse TraceMiner kinds like ``string-0-count-I-mod-3-in-1-2``."""
    if not kind or "-count-" not in kind or "-mod-" not in kind:
        return None
    try:
        after = kind.split("-count-", 1)[1]
        char, rest = after.split("-mod-", 1)
        if not char or len(char) != 1:
            return None
        if "-in-" in rest:
            mod_s, res_s = rest.split("-in-", 1)
            modulus = int(mod_s)
            residues = frozenset(int(x) for x in res_s.split("-") if x != "")
        else:
            parts = rest.split("-")
            modulus = int(parts[0])
            residues = frozenset({int(parts[1])}) if len(parts) > 1 else None
            if residues is None:
                return None
        if modulus < 2 or not residues:
            return None
        if any(r < 0 or r >= modulus for r in residues):
            return None
        return char, modulus, residues
    except (ValueError, IndexError):
        return None


def _flatten_concat(expr: z3.ExprRef) -> list[z3.ExprRef] | None:
    """Flatten a tree of ``str.++`` into leaves; None if unsupported."""
    if z3.is_string_value(expr):
        return [expr]
    if z3.is_app(expr) and expr.decl().kind() == z3.Z3_OP_SEQ_CONCAT:
        parts: list[z3.ExprRef] = []
        for i in range(expr.num_args()):
            sub = _flatten_concat(expr.arg(i))
            if sub is None:
                return None
            parts.extend(sub)
        return parts
    if z3.is_const(expr) and not z3.is_string_value(expr):
        return [expr]
    return None


def _eq_sides(body: z3.BoolRef) -> list[tuple[z3.ExprRef, z3.ExprRef]]:
    """Collect equality pairs from a (possibly nested) And of equalities."""
    pairs: list[tuple[z3.ExprRef, z3.ExprRef]] = []

    def walk(e: z3.ExprRef) -> None:
        if z3.is_eq(e) and e.num_args() == 2:
            pairs.append((e.arg(0), e.arg(1)))
            return
        if z3.is_and(e):
            for i in range(e.num_args()):
                walk(e.arg(i))

    walk(body)
    return pairs


def _count_coeff(
    parts: list[z3.ExprRef], char: str
) -> tuple[int, dict[int, int]] | None:
    """Return (literal_count, {var_id: coefficient}) for count of *char*."""
    lit = 0
    coeffs: dict[int, int] = {}
    for p in parts:
        if z3.is_string_value(p):
            lit += p.as_string().count(char)
        elif z3.is_const(p):
            coeffs[p.get_id()] = coeffs.get(p.get_id(), 0) + 1
        else:
            return None
    return lit, coeffs


def _arithmetic_count_modulo_preserved(rule: HornRule, kind: str) -> bool | None:
    """True if *rule* preserves the count-modulo invariant named by *kind*.

    Analyzes word-equation transitions ``vi = concat(...)``, ``vo = concat(...)``
    and checks that every residue in the observed set is mapped into the set
    under the linear effect on ``count(char)``. Returns ``None`` when the rule
    or kind cannot be analyzed this way.

    SOUNDNESS REQUIREMENT: this function proves preservation by assuming
    "count(char, vi) mod modulus in residues" as a hypothesis (the same
    fact the caller is trying to establish for vo) and deriving the goal
    algebraically from the rule's own defining equalities. That hypothesis
    is only justified when it is something Houdini is actually assuming
    elsewhere in the SAME induction step -- i.e. when the identical
    candidate (same key, same residues) is a live hypothesis for
    ``rule.src_relation``. The only case this file can cheaply guarantee
    that in is a genuine self-loop (``rule.src_relation is rule.dst_relation``):
    every caller already restricts to keys currently active for
    ``rule.dst_relation`` before calling this function, and for a
    self-loop that is *the same relation*, so "active for the
    destination" and "active for the source" are the same fact by
    construction. For rule.src_relation != rule.dst_relation there is no
    such guarantee -- the destination candidate's kind label says nothing
    about what (if anything) is actually retained for the source
    relation, so assuming it here would be unsound. Refusing this case
    falls back to a real SMT/regex check, which is always safe (only
    costs precision, never correctness). Confirmed by construction: see
    tests/test_trace_houdini.py::
    test_multi_houdini_rejects_unsound_cross_relation_count_modulo_candidate.
    """
    parsed = _parse_count_modulo_kind(kind)
    if parsed is None:
        return None
    char, modulus, residues = parsed
    if rule.is_query or rule.src_relation is None:
        return None
    if rule.src_relation != rule.dst_relation:
        return None
    if len(rule.src_args) != 1 or len(rule.dst_args) != 1:
        return None
    vi, vo = rule.src_args[0], rule.dst_args[0]
    pairs = _eq_sides(rule.body)
    vi_rhs = vo_rhs = None
    for lhs, rhs in pairs:
        if lhs.eq(vi):
            vi_rhs = rhs
        elif rhs.eq(vi):
            vi_rhs = lhs
        if lhs.eq(vo):
            vo_rhs = rhs
        elif rhs.eq(vo):
            vo_rhs = lhs
    if vi_rhs is None or vo_rhs is None:
        return None
    vi_parts = _flatten_concat(vi_rhs)
    vo_parts = _flatten_concat(vo_rhs)
    if vi_parts is None or vo_parts is None:
        return None
    vi_c = _count_coeff(vi_parts, char)
    vo_c = _count_coeff(vo_parts, char)
    if vi_c is None or vo_c is None:
        return None
    vi_lit, vi_vars = vi_c
    vo_lit, vo_vars = vo_c
    # Support pure affine maps count_vo = a * count_vi + b when both sides
    # share at most one common variable coefficient pattern, or when the
    # effect is a constant shift (identical variable multisets).
    # Case 1: same variable multiset → constant shift vo_lit - vi_lit.
    if vi_vars == vo_vars:
        delta = (vo_lit - vi_lit) % modulus
        return all((r + delta) % modulus in residues for r in residues)
    # Case 2: doubling pattern vo = M++x++x, vi = M++x (one var, coeff 2 vs 1).
    if len(vi_vars) == 1 and len(vo_vars) == 1:
        (vid, vc), = vi_vars.items()
        (wod, wc), = vo_vars.items()
        if vid == wod and vc > 0 and wc % vc == 0:
            factor = wc // vc
            # count_vo ≡ factor * (count_vi - vi_lit) + vo_lit
            #          ≡ factor * count_vi + (vo_lit - factor * vi_lit)
            b = (vo_lit - factor * vi_lit) % modulus
            return all(
                (factor * r + b) % modulus in residues for r in residues
            )
    return None
