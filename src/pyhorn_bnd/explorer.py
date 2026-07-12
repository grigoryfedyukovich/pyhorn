"""Exhaustive increasing-size bounded exploration of normalized CHCs."""

from __future__ import annotations

from dataclasses import dataclass, field
from enum import Enum
from pathlib import Path
from time import perf_counter
from typing import Iterator

import z3

from .horn import ENTRY, HornProgram, HornRule
from .solver_pool import IncrementalSolverPool, SolverPoolStatistics
from .vc import (
    SSAConstructionStatistics,
    VerificationCondition,
    VerificationConditionBuilder,
)


class CheckStatus(str, Enum):
    SAT = "sat"
    UNSAT = "unsat"
    UNKNOWN = "unknown"


class ExplorationStatus(str, Enum):
    COUNTEREXAMPLE = "counterexample"
    BOUNDED_SAFE = "bounded-safe"
    COMPLETE_SAFE = "complete-safe"
    UNKNOWN = "unknown"
    EMPTY = "empty"


@dataclass(frozen=True)
class TraceCheck:
    status: CheckStatus
    vc: VerificationCondition
    elapsed_seconds: float
    unsat_prefix_length: int | None = None
    reason_unknown: str | None = None
    model: z3.ModelRef | None = None


@dataclass(frozen=True)
class DepthStatistics:
    depth: int
    generated: int
    checked: int
    pruned: int
    elapsed_seconds: float


@dataclass(frozen=True)
class ExplorationResult:
    status: ExplorationStatus
    requested_upto: int
    explored_upto: int
    complete: bool
    depth_statistics: tuple[DepthStatistics, ...]
    trace_check: TraceCheck | None = None


@dataclass
class _PrefixNode:
    terminal: bool = False
    children: dict[int, "_PrefixNode"] = field(default_factory=dict)


class UnsatPrefixSet:
    """Trie of rule-id prefixes proven infeasible by incremental SMT checks."""

    def __init__(self) -> None:
        self._root = _PrefixNode()

    def add(self, prefix: tuple[int, ...]) -> None:
        node = self._root
        for rule_id in prefix:
            if node.terminal:
                return
            node = node.children.setdefault(rule_id, _PrefixNode())
        node.terminal = True
        node.children.clear()

    def subsumes(self, trace: tuple[int, ...]) -> bool:
        node = self._root
        if node.terminal:
            return True
        for rule_id in trace:
            child = node.children.get(rule_id)
            if child is None:
                return False
            node = child
            if node.terminal:
                return True
        return False


class BoundedExplorer:
    def __init__(
        self,
        program: HornProgram,
        *,
        timeout_ms: int = 1000,
        random_seed: int | None = None,
        ssa_dump_dir: Path | str | None = None,
        use_solver_pool: bool = True,
        solver_reuse_min_ratio: float = 1.0 / 3.0,
        max_solver_contexts: int | None = None,
    ) -> None:
        if timeout_ms < 0:
            raise ValueError("timeout_ms must be non-negative")
        self.program = program
        self.timeout_ms = timeout_ms
        self.random_seed = random_seed
        self.unsat_prefixes = UnsatPrefixSet()
        self.vc_builder = VerificationConditionBuilder(program)
        self.solver_pool = IncrementalSolverPool(
            timeout_ms=timeout_ms,
            random_seed=random_seed,
            enabled=use_solver_pool,
            reuse_min_ratio=solver_reuse_min_ratio,
            max_contexts=max_solver_contexts,
        )
        self.ssa_dump_dir = (
            None if ssa_dump_dir is None else Path(ssa_dump_dir).resolve()
        )
        self._ssa_dump_count = 0
        if self.ssa_dump_dir is not None:
            if self.ssa_dump_dir.exists() and not self.ssa_dump_dir.is_dir():
                raise ValueError(
                    f"SSA dump path is not a directory: {self.ssa_dump_dir}"
                )
            self.ssa_dump_dir.mkdir(parents=True, exist_ok=True)
            if any(self.ssa_dump_dir.iterdir()):
                raise ValueError(
                    "SSA dump directory must be empty to avoid mixing or "
                    f"overwriting runs: {self.ssa_dump_dir}"
                )

    @property
    def ssa_dump_count(self) -> int:
        return self._ssa_dump_count

    @property
    def solver_statistics(self) -> SolverPoolStatistics:
        return self.solver_pool.statistics

    @property
    def ssa_statistics(self) -> SSAConstructionStatistics:
        return self.vc_builder.statistics

    def _dump_ssa(self, vc: VerificationCondition) -> Path | None:
        if self.ssa_dump_dir is None:
            return None

        self._ssa_dump_count += 1
        destination = self.ssa_dump_dir / (
            f"ssa_{self._ssa_dump_count:06d}_depth_{len(vc.trace):06d}.smt2"
        )
        temporary = destination.with_suffix(".smt2.tmp")
        temporary.write_text(vc.to_smt2(), encoding="utf-8")
        temporary.replace(destination)
        return destination

    def traces_of_length(self, length: int) -> Iterator[tuple[HornRule, ...]]:
        if length < 1:
            return

        # Use an explicit stack: the C++ default bound is 10,000, well above
        # Python's recursion limit. Reversing outgoing rules preserves source
        # order under LIFO traversal.
        stack: list[tuple[z3.FuncDeclRef | None, int, tuple[HornRule, ...]]] = [
            (ENTRY, length, ())
        ]
        while stack:
            relation, remaining, trace = stack.pop()
            for rule in reversed(self.program.outgoing.get(relation, ())):
                candidate = trace + (rule,)
                ids = tuple(item.rule_id for item in candidate)
                if self.unsat_prefixes.subsumes(ids):
                    continue
                reaches_query = rule.dst_relation in self.program.query_relations
                if remaining == 1:
                    if reaches_query:
                        yield candidate
                elif not reaches_query:
                    stack.append((rule.dst_relation, remaining - 1, candidate))

    def check_trace(self, trace: tuple[HornRule, ...]) -> TraceCheck:
        started = perf_counter()
        vc = self.vc_builder.build(trace)
        # Dump immediately after SSA construction, before any solver result can
        # influence what is written. The file therefore represents precisely
        # the VC constructed for this candidate trace.
        self._dump_ssa(vc)

        pool_check = self.solver_pool.check(vc)
        elapsed = perf_counter() - started
        if pool_check.result == z3.unsat:
            return TraceCheck(
                status=CheckStatus.UNSAT,
                vc=vc,
                elapsed_seconds=elapsed,
                unsat_prefix_length=pool_check.checked_prefix_length,
            )
        if pool_check.result == z3.unknown:
            return TraceCheck(
                status=CheckStatus.UNKNOWN,
                vc=vc,
                elapsed_seconds=elapsed,
                reason_unknown=pool_check.reason_unknown,
            )

        return TraceCheck(
            status=CheckStatus.SAT,
            vc=vc,
            elapsed_seconds=elapsed,
            model=pool_check.model,
        )

    def explore(self, *, start: int = 1, upto: int = 10_000) -> ExplorationResult:
        if start < 1:
            raise ValueError("start must be at least 1")
        if upto < start:
            raise ValueError("upto must be greater than or equal to start")
        if not self.program.rules or not self.program.outgoing.get(ENTRY):
            return ExplorationResult(
                status=ExplorationStatus.EMPTY,
                requested_upto=upto,
                explored_upto=0,
                complete=True,
                depth_statistics=(),
            )

        acyclic_max = self.program.maximum_acyclic_trace_length()
        effective_upto = upto if acyclic_max is None else min(upto, acyclic_max)
        stats: list[DepthStatistics] = []
        explored_upto = 0

        for depth in range(start, effective_upto + 1):
            depth_start = perf_counter()
            generated = checked = pruned = 0
            # Count pruned candidates at generation time by comparing prefix-trie
            # effects indirectly is expensive; generated means yielded complete
            # traces, while pruned records newly learned infeasible prefixes.
            for trace in self.traces_of_length(depth):
                generated += 1
                checked += 1
                check = self.check_trace(trace)
                if check.status is CheckStatus.UNSAT:
                    assert check.unsat_prefix_length is not None
                    prefix = check.vc.rule_ids[: check.unsat_prefix_length]
                    self.unsat_prefixes.add(prefix)
                    pruned += 1
                    continue

                stats.append(
                    DepthStatistics(
                        depth=depth,
                        generated=generated,
                        checked=checked,
                        pruned=pruned,
                        elapsed_seconds=perf_counter() - depth_start,
                    )
                )
                status = (
                    ExplorationStatus.COUNTEREXAMPLE
                    if check.status is CheckStatus.SAT
                    else ExplorationStatus.UNKNOWN
                )
                return ExplorationResult(
                    status=status,
                    requested_upto=upto,
                    explored_upto=depth,
                    complete=False,
                    depth_statistics=tuple(stats),
                    trace_check=check,
                )

            explored_upto = depth
            stats.append(
                DepthStatistics(
                    depth=depth,
                    generated=generated,
                    checked=checked,
                    pruned=pruned,
                    elapsed_seconds=perf_counter() - depth_start,
                )
            )

        complete = (
            start == 1 and acyclic_max is not None and effective_upto >= acyclic_max
        )
        return ExplorationResult(
            status=(
                ExplorationStatus.COMPLETE_SAFE
                if complete
                else ExplorationStatus.BOUNDED_SAFE
            ),
            requested_upto=upto,
            explored_upto=explored_upto,
            complete=complete,
            depth_statistics=tuple(stats),
        )
