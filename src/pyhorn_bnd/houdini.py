"""Multi-predicate Houdini filtering for seed-mined CHC candidates."""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum
from typing import Collection, Mapping

import z3
from z3.z3util import get_vars

from .horn import HornProgram, HornRule
from .seedminer import CandidateMap, SeedMiner, SeedMiningResult, VariableMap


class HoudiniStatus(Enum):
    SUCCESS = "success"
    UNKNOWN = "unknown"


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
    ):
        if timeout_ms < 0:
            raise ValueError("timeout_ms must be non-negative")
        self.program = program
        self.variables = variables
        self.timeout_ms = timeout_ms
        self.random_seed = random_seed

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
                    unknown_checks += 1
                    failures.append(
                        HoudiniFailure(
                            rule_id=rule.rule_id,
                            rule=rule.short(),
                            reason=outcome.reason_unknown or "Z3 returned unknown",
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
                    continue

                if outcome.model is None:
                    raise RuntimeError("SAT Houdini check returned no model")
                model = outcome.model
                countermodels += 1
                bad = [
                    key
                    for key, formula in context.destination_formulas.items()
                    if key in destination
                    and z3.is_false(model.eval(formula, model_completion=True))
                ]
                if not bad:
                    # The asserted disjunction guarantees at least one false
                    # destination formula.  Retain a defensive fallback for
                    # unusual model-evaluation behavior.
                    bad = [
                        key
                        for key, formula in context.destination_formulas.items()
                        if key in destination
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
        violated = [
            z3.Not(formula)
            for key, formula in context.destination_formulas.items()
            if key in destination
        ]
        if not violated:
            return _SolverOutcome(z3.unsat, None)
        assumptions = self._active_source_assumptions(context, active)
        context.solver.push()
        try:
            context.solver.add(z3.Or(*violated))
            result = context.solver.check(*assumptions)
            model = context.solver.model() if result == z3.sat else None
            reason = (
                context.solver.reason_unknown() if result == z3.unknown else None
            )
            return _SolverOutcome(result, model, reason)
        finally:
            context.solver.pop()

    def _probe_refuted_destination_candidates(
        self,
        context: _RuleContext,
        active: Mapping[z3.FuncDeclRef, Mapping[str, z3.BoolRef]],
        destination: Mapping[str, z3.BoolRef],
    ) -> tuple[list[str], int, str | None]:
        """Find candidates refuted individually when model evaluation is partial."""

        assumptions = self._active_source_assumptions(context, active)
        bad: list[str] = []
        checks = 0
        first_unknown: str | None = None
        for key, formula in context.destination_formulas.items():
            if key not in destination:
                continue
            context.solver.push()
            try:
                context.solver.add(z3.Not(formula))
                result = context.solver.check(*assumptions)
                checks += 1
                if result == z3.sat:
                    bad.append(key)
                elif result == z3.unknown and first_unknown is None:
                    first_unknown = (
                        context.solver.reason_unknown() or "Z3 returned unknown"
                    )
            finally:
                context.solver.pop()
        return bad, checks, first_unknown

    def _certify_fresh(
        self,
        rule: HornRule,
        active: Mapping[z3.FuncDeclRef, Mapping[str, z3.BoolRef]],
    ) -> tuple[_SolverOutcome, bool]:
        """Validate one final CHC using a solver with no filtering history."""

        if not rule.is_query and not active.get(rule.dst_relation, {}):
            # The destination invariant is ``true``.
            return _SolverOutcome(z3.unsat, None), False

        solver = z3.Solver()
        solver.set(timeout=self.timeout_ms)
        if self.random_seed is not None:
            solver.set(random_seed=self.random_seed)
        solver.add(rule.body)

        if rule.src_relation is not None and rule.src_relation in self.variables:
            for candidate in active.get(rule.src_relation, {}).values():
                solver.add(
                    self._instantiate(rule.src_relation, candidate, rule.src_args)
                )

        if not rule.is_query:
            violated = [
                z3.Not(
                    self._instantiate(rule.dst_relation, candidate, rule.dst_args)
                )
                for candidate in active.get(rule.dst_relation, {}).values()
            ]
            if not violated:
                return _SolverOutcome(z3.unsat, None), False
            solver.add(z3.Or(*violated))

        result = solver.check()
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
) -> HoudiniResult:
    """Mine candidates, run MultiHoudini, and validate all CHCs."""

    seeds = SeedMiner(program).mine()
    result = MultiHoudini(
        program,
        seeds.variables,
        timeout_ms=timeout_ms,
        random_seed=random_seed,
    ).run(seeds.candidates, seed_result=seeds)
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
