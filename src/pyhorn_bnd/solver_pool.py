"""Fresh and cross-trace incremental Z3 solver backends."""

from __future__ import annotations

from dataclasses import dataclass

import z3

from .vc import VerificationCondition

DEFAULT_MAX_SOLVERS = 16


@dataclass(frozen=True)
class SolverPoolStatistics:
    """Common statistics reported by both solver backends.

    In fresh mode, ``contexts`` and all reuse/push/pop counters are zero, while
    ``solvers_created`` equals the number of traces checked.
    """

    contexts: int
    solvers_created: int
    contexts_recycled: int
    traces_reused: int
    exact_prefix_hits: int
    common_prefix_steps_reused: int
    pushes: int
    pops: int
    checks: int


@dataclass(frozen=True)
class SolverPoolCheck:
    result: z3.CheckSatResult
    checked_prefix_length: int
    context_id: int | None
    common_prefix_length: int
    created_context: bool
    popped_steps: int
    pushed_steps: int
    reason_unknown: str | None = None
    model: z3.ModelRef | None = None


class FreshTraceSolver:
    """Original baseline: one fresh solver for every candidate trace.

    The solver is extended monotonically with one SSA step at a time and
    checked after every addition so that the first infeasible prefix can be
    learned. No solver state survives across traces, and this backend never
    calls ``push()`` or ``pop()``.
    """

    def __init__(
        self,
        *,
        timeout_ms: int = 1000,
        random_seed: int | None = None,
    ) -> None:
        if timeout_ms < 0:
            raise ValueError("timeout_ms must be non-negative")
        self.timeout_ms = timeout_ms
        self.random_seed = random_seed
        self._solvers_created = 0
        self._checks = 0
        self._last_check: SolverPoolCheck | None = None

    @property
    def statistics(self) -> SolverPoolStatistics:
        return SolverPoolStatistics(
            contexts=0,
            solvers_created=self._solvers_created,
            contexts_recycled=0,
            traces_reused=0,
            exact_prefix_hits=0,
            common_prefix_steps_reused=0,
            pushes=0,
            pops=0,
            checks=self._checks,
        )

    @property
    def last_check(self) -> SolverPoolCheck | None:
        return self._last_check

    @property
    def context_prefixes(self) -> tuple[tuple[int, ...], ...]:
        return ()

    def _make_solver(self) -> z3.Solver:
        solver = z3.Solver()
        if self.timeout_ms:
            solver.set(timeout=self.timeout_ms)
        if self.random_seed is not None:
            solver.set(random_seed=self.random_seed)
        self._solvers_created += 1
        return solver

    def check(self, vc: VerificationCondition) -> SolverPoolCheck:
        solver = self._make_solver()

        for index, step in enumerate(vc.steps):
            solver.add(step.constraint)
            result = solver.check()
            self._checks += 1

            if result == z3.sat:
                continue

            check = SolverPoolCheck(
                result=result,
                checked_prefix_length=index + 1,
                context_id=None,
                common_prefix_length=0,
                created_context=True,
                popped_steps=0,
                pushed_steps=0,
                reason_unknown=(
                    solver.reason_unknown() if result == z3.unknown else None
                ),
            )
            self._last_check = check
            return check

        check = SolverPoolCheck(
            result=z3.sat,
            checked_prefix_length=len(vc.steps),
            context_id=None,
            common_prefix_length=0,
            created_context=True,
            popped_steps=0,
            pushed_steps=0,
            model=solver.model(),
        )
        self._last_check = check
        return check


@dataclass
class _SolverContext:
    context_id: int
    solver: z3.Solver
    rule_ids: list[int]
    last_used: int
    last_model: z3.ModelRef | None = None


class IncrementalSolverPool:
    """Pool of mutable incremental solvers indexed by their SAT trace prefix.

    A candidate VC selects the context with the longest common rule prefix.
    When that prefix is sufficiently large, the context is popped back to the
    fork point and extended with the new suffix. Otherwise a new context is
    allocated (or an LRU context is recycled when a limit is configured).

    Every retained scope is known SAT. If a newly pushed constraint is UNSAT or
    unknown, that scope is immediately popped before returning.
    """

    def __init__(
        self,
        *,
        timeout_ms: int = 1000,
        random_seed: int | None = None,
        reuse_min_ratio: float = 1.0 / 3.0,
        max_contexts: int | None = DEFAULT_MAX_SOLVERS,
    ) -> None:
        if timeout_ms < 0:
            raise ValueError("timeout_ms must be non-negative")
        if not 0.0 <= reuse_min_ratio <= 1.0:
            raise ValueError("reuse_min_ratio must be between 0 and 1")
        if max_contexts is not None and max_contexts < 1:
            raise ValueError("max_contexts must be positive or None")

        self.timeout_ms = timeout_ms
        self.random_seed = random_seed
        self.reuse_min_ratio = reuse_min_ratio
        self.max_contexts = max_contexts
        self._contexts: list[_SolverContext] = []
        self._contexts_by_first_rule: dict[int, list[_SolverContext]] = {}
        self._next_context_id = 0
        self._clock = 0
        self._solvers_created = 0
        self._contexts_recycled = 0
        self._traces_reused = 0
        self._exact_prefix_hits = 0
        self._common_prefix_steps_reused = 0
        self._pushes = 0
        self._pops = 0
        self._checks = 0
        self._last_check: SolverPoolCheck | None = None

    @property
    def statistics(self) -> SolverPoolStatistics:
        return SolverPoolStatistics(
            contexts=len(self._contexts),
            solvers_created=self._solvers_created,
            contexts_recycled=self._contexts_recycled,
            traces_reused=self._traces_reused,
            exact_prefix_hits=self._exact_prefix_hits,
            common_prefix_steps_reused=self._common_prefix_steps_reused,
            pushes=self._pushes,
            pops=self._pops,
            checks=self._checks,
        )

    @property
    def last_check(self) -> SolverPoolCheck | None:
        return self._last_check

    @property
    def context_prefixes(self) -> tuple[tuple[int, ...], ...]:
        """Expose immutable rule-prefix snapshots for diagnostics and tests."""
        return tuple(tuple(context.rule_ids) for context in self._contexts)

    def _make_solver(self) -> z3.Solver:
        solver = z3.Solver()
        if self.timeout_ms:
            solver.set(timeout=self.timeout_ms)
        if self.random_seed is not None:
            solver.set(random_seed=self.random_seed)
        self._solvers_created += 1
        return solver

    def _new_or_recycled_context(self) -> _SolverContext:
        self._clock += 1
        if (
            self.max_contexts is not None
            and len(self._contexts) >= self.max_contexts
        ):
            victim = min(self._contexts, key=lambda item: item.last_used)
            # Reuse the physical Z3 solver object so the configured limit also
            # bounds solver allocations and their native memory. ``reset()``
            # removes every assertion and backtracking scope.
            self._remove_from_index(victim)
            victim.solver.reset()
            if self.timeout_ms:
                victim.solver.set(timeout=self.timeout_ms)
            if self.random_seed is not None:
                victim.solver.set(random_seed=self.random_seed)
            victim.rule_ids.clear()
            victim.last_model = None
            victim.last_used = self._clock
            self._contexts_recycled += 1
            return victim

        context = _SolverContext(
            context_id=self._next_context_id,
            solver=self._make_solver(),
            rule_ids=[],
            last_used=self._clock,
        )
        self._next_context_id += 1
        self._contexts.append(context)
        return context

    def _remove_from_index(self, context: _SolverContext) -> None:
        if not context.rule_ids:
            return
        first_rule = context.rule_ids[0]
        bucket = self._contexts_by_first_rule.get(first_rule)
        if bucket is None:
            return
        bucket[:] = [item for item in bucket if item is not context]
        if not bucket:
            del self._contexts_by_first_rule[first_rule]

    def _index_context(self, context: _SolverContext) -> None:
        if not context.rule_ids:
            return
        bucket = self._contexts_by_first_rule.setdefault(context.rule_ids[0], [])
        if all(item is not context for item in bucket):
            bucket.append(context)

    @staticmethod
    def _common_prefix_length(left: list[int], right: tuple[int, ...]) -> int:
        size = min(len(left), len(right))
        index = 0
        while index < size and left[index] == right[index]:
            index += 1
        return index

    def _select_context(
        self, rule_ids: tuple[int, ...]
    ) -> tuple[_SolverContext, int, bool]:
        if not self._contexts:
            return self._new_or_recycled_context(), 0, True

        best_context: _SolverContext | None = None
        best_prefix = 0
        candidates = self._contexts_by_first_rule.get(rule_ids[0], ())
        for context in candidates:
            prefix = self._common_prefix_length(context.rule_ids, rule_ids)
            if prefix > best_prefix:
                best_context = context
                best_prefix = prefix

        # Match Aeval's strict ``csz > v.size() / 3`` policy by default.
        sufficiently_large = best_prefix > len(rule_ids) * self.reuse_min_ratio
        if best_context is None or not sufficiently_large:
            return self._new_or_recycled_context(), 0, True

        self._traces_reused += 1
        self._common_prefix_steps_reused += best_prefix
        if best_prefix == len(rule_ids):
            self._exact_prefix_hits += 1
        self._clock += 1
        best_context.last_used = self._clock
        return best_context, best_prefix, False

    def check(self, vc: VerificationCondition) -> SolverPoolCheck:
        rule_ids = vc.rule_ids
        context, common_prefix, created = self._select_context(rule_ids)

        popped_steps = len(context.rule_ids) - common_prefix
        if popped_steps:
            context.solver.pop(popped_steps)
            del context.rule_ids[common_prefix:]
            context.last_model = None
            self._pops += popped_steps

        pushed_steps = 0
        if common_prefix < len(vc.steps):
            context.last_model = None
        for index in range(common_prefix, len(vc.steps)):
            step = vc.steps[index]
            context.solver.push()
            context.solver.add(step.constraint)
            self._pushes += 1
            pushed_steps += 1

            result = context.solver.check()
            self._checks += 1
            if result == z3.sat:
                context.rule_ids.append(rule_ids[index])
                if len(context.rule_ids) == 1:
                    self._index_context(context)
                continue

            reason_unknown = (
                context.solver.reason_unknown() if result == z3.unknown else None
            )
            # Keep only the preceding SAT prefix in the reusable context.
            context.solver.pop()
            self._pops += 1
            check = SolverPoolCheck(
                result=result,
                checked_prefix_length=index + 1,
                context_id=context.context_id,
                common_prefix_length=common_prefix,
                created_context=created,
                popped_steps=popped_steps + 1,
                pushed_steps=pushed_steps,
                reason_unknown=reason_unknown,
            )
            self._last_check = check
            return check

        result = z3.sat
        if pushed_steps:
            # The final suffix check was SAT at the current full context.
            context.last_model = context.solver.model()
        # Exact repeated traces can reuse the model captured when the same SAT
        # context was first established. If the context was popped to a shorter
        # exact prefix, its old model is invalid and one re-check is necessary.
        if context.last_model is None:
            result = context.solver.check()
            self._checks += 1
            if result == z3.sat:
                context.last_model = context.solver.model()

        model = context.last_model if result == z3.sat else None
        reason_unknown = context.solver.reason_unknown() if result == z3.unknown else None
        check = SolverPoolCheck(
            result=result,
            checked_prefix_length=len(vc.steps),
            context_id=context.context_id,
            common_prefix_length=common_prefix,
            created_context=created,
            popped_steps=popped_steps,
            pushed_steps=pushed_steps,
            reason_unknown=reason_unknown,
            model=model,
        )
        self._last_check = check
        return check
