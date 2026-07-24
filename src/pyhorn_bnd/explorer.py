"""Exhaustive increasing-size bounded exploration of normalized CHCs."""

from __future__ import annotations

from dataclasses import dataclass, field
from enum import Enum
from pathlib import Path
from time import perf_counter
from typing import Iterator

import z3

from .horn import ENTRY, HornProgram, HornRule
from .solver_pool import (
    DEFAULT_MAX_SOLVERS,
    FreshTraceSolver,
    IncrementalSolverPool,
    SolverPoolStatistics,
)
from .vc import (
    BndExplSmtDumpBuilder,
    DEFAULT_MAX_SSA_CACHE_STEPS,
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


@dataclass(frozen=True, slots=True)
class _TracePath:
    parent: "_TracePath | None"
    rule: HornRule
    length: int

    def to_tuple(self) -> tuple[HornRule, ...]:
        items: list[HornRule | None] = [None] * self.length
        current: _TracePath | None = self
        index = self.length - 1
        while current is not None:
            items[index] = current.rule
            current = current.parent
            index -= 1
        if any(item is None for item in items):
            raise RuntimeError("incomplete internal trace path")
        return tuple(item for item in items if item is not None)

    def rule_ids(self) -> tuple[int, ...]:
        return tuple(rule.rule_id for rule in self.to_tuple())


@dataclass(frozen=True, slots=True)
class _PrefixCursor:
    node: _PrefixNode | None
    revision: int


class UnsatPrefixSet:
    """Trie of rule-id prefixes proven infeasible by incremental SMT checks."""

    def __init__(self) -> None:
        self._root = _PrefixNode()
        self._revision = 0

    @property
    def root_cursor(self) -> _PrefixCursor:
        return _PrefixCursor(self._root, self._revision)

    def add(self, prefix: tuple[int, ...]) -> None:
        node = self._root
        for rule_id in prefix:
            if node.terminal:
                return
            node = node.children.setdefault(rule_id, _PrefixNode())
        if node.terminal:
            return
        node.terminal = True
        node.children.clear()
        self._revision += 1

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

    def _cursor_for_path(self, path: _TracePath | None) -> _PrefixCursor:
        node: _PrefixNode | None = self._root
        if path is not None:
            for rule_id in path.rule_ids():
                if node is None:
                    break
                node = node.children.get(rule_id)
        return _PrefixCursor(node, self._revision)

    def advance(
        self,
        path: _TracePath | None,
        cursor: _PrefixCursor,
        rule_id: int,
    ) -> tuple[_PrefixCursor, bool]:
        if cursor.revision != self._revision:
            cursor = self._cursor_for_path(path)
        child = None if cursor.node is None else cursor.node.children.get(rule_id)
        next_cursor = _PrefixCursor(child, self._revision)
        return next_cursor, child is not None and child.terminal


class BoundedExplorer:
    def __init__(
        self,
        program: HornProgram,
        *,
        timeout_ms: int = 1000,
        random_seed: int | None = None,
        smt_dump_dir: Path | str | None = None,
        solver_mode: str = "pool",
        solver_reuse_min_ratio: float = 1.0 / 3.0,
        max_solver_contexts: int | None = DEFAULT_MAX_SOLVERS,
        max_cached_ssa_steps: int | None = DEFAULT_MAX_SSA_CACHE_STEPS,
    ) -> None:
        if timeout_ms < 0:
            raise ValueError("timeout_ms must be non-negative")
        if solver_mode not in {"pool", "fresh"}:
            raise ValueError("solver_mode must be 'pool' or 'fresh'")
        self.program = program
        self.timeout_ms = timeout_ms
        self.random_seed = random_seed
        self.solver_mode = solver_mode
        self.max_solver_contexts = (
            max_solver_contexts if solver_mode == "pool" else None
        )
        self.unsat_prefixes = UnsatPrefixSet()
        self.vc_builder = VerificationConditionBuilder(
            program,
            max_cached_steps=max_cached_ssa_steps,
        )
        self.smt_dump_builder = BndExplSmtDumpBuilder(program)
        if solver_mode == "pool":
            self.solver_backend = IncrementalSolverPool(
                timeout_ms=timeout_ms,
                random_seed=random_seed,
                reuse_min_ratio=solver_reuse_min_ratio,
                max_contexts=max_solver_contexts,
            )
        else:
            self.solver_backend = FreshTraceSolver(
                timeout_ms=timeout_ms,
                random_seed=random_seed,
            )
        self.smt_dump_dir = (
            None if smt_dump_dir is None else Path(smt_dump_dir).resolve()
        )
        self._smt_dump_count = 0
        if self.smt_dump_dir is not None:
            if self.smt_dump_dir.exists() and not self.smt_dump_dir.is_dir():
                raise NotADirectoryError(
                    f"SMT dump path is not a directory: {self.smt_dump_dir}"
                )
            self.smt_dump_dir.mkdir(parents=True, exist_ok=True)

    @property
    def smt_dump_count(self) -> int:
        return self._smt_dump_count

    @property
    def solver_statistics(self) -> SolverPoolStatistics:
        return self.solver_backend.statistics

    @property
    def ssa_statistics(self) -> SSAConstructionStatistics:
        return self.vc_builder.statistics

    def _dump_smt(
        self,
        check: TraceCheck,
        *,
        bound: int,
        trace_number: int,
        trace_count: int,
    ) -> Path | None:
        if self.smt_dump_dir is None:
            return None

        stem = self.program.source_path.stem
        suffix = f"{stem}_k{bound}"
        if trace_count > 1:
            suffix += f"_t{trace_number}"
        suffix += f"_{check.status.value}.smt2"
        destination = self.smt_dump_dir / suffix
        temporary = destination.with_suffix(".smt2.tmp")
        temporary.write_text(
            self.smt_dump_builder.to_smt2(
                check.vc.trace,
                bound=bound,
                result=check.status.value,
            ),
            encoding="utf-8",
        )
        temporary.replace(destination)
        self._smt_dump_count += 1
        return destination

    def traces_of_length(self, length: int) -> Iterator[tuple[HornRule, ...]]:
        if length < 1:
            return

        # Use an explicit stack: the C++ default bound is 10,000, well above
        # Python's recursion limit. Reversing outgoing rules preserves source
        # order under LIFO traversal.
        stack: list[
            tuple[
                z3.FuncDeclRef | None,
                int,
                _TracePath | None,
                _PrefixCursor,
            ]
        ] = [
            (ENTRY, length, None, self.unsat_prefixes.root_cursor)
        ]
        while stack:
            relation, remaining, path, cursor = stack.pop()
            for rule in reversed(self.program.outgoing.get(relation, ())):
                next_cursor, subsumed = self.unsat_prefixes.advance(
                    path,
                    cursor,
                    rule.rule_id,
                )
                if subsumed:
                    continue
                candidate = _TracePath(
                    parent=path,
                    rule=rule,
                    length=1 if path is None else path.length + 1,
                )
                reaches_query = rule.dst_relation in self.program.query_relations
                if remaining == 1:
                    if reaches_query:
                        yield candidate.to_tuple()
                elif not reaches_query:
                    stack.append(
                        (
                            rule.dst_relation,
                            remaining - 1,
                            candidate,
                            next_cursor,
                        )
                    )

    def check_trace(self, trace: tuple[HornRule, ...]) -> TraceCheck:
        started = perf_counter()
        vc = self.vc_builder.build(trace)
        pool_check = self.solver_backend.check(vc)
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
            traces: Iterator[tuple[HornRule, ...]] | tuple[tuple[HornRule, ...], ...]
            trace_count = 0
            decisive_check: TraceCheck | None = None
            if self.smt_dump_dir is None:
                traces = self.traces_of_length(depth)
            else:
                # The C++ explorer collects all traces for a bound before
                # checking any of them. This also fixes the total trace count
                # used by the ``_tN`` filename convention.
                materialized = tuple(self.traces_of_length(depth))
                traces = materialized
                trace_count = len(materialized)

            for trace_number, trace in enumerate(traces, start=1):
                generated += 1
                checked += 1
                check = self.check_trace(trace)
                if self.smt_dump_dir is not None:
                    self._dump_smt(
                        check,
                        bound=depth,
                        trace_number=trace_number,
                        trace_count=trace_count,
                    )
                if check.status is CheckStatus.UNSAT:
                    if check.unsat_prefix_length is None:
                        raise RuntimeError(
                            "solver backend returned UNSAT without a prefix length"
                        )
                    prefix = check.vc.rule_ids[: check.unsat_prefix_length]
                    self.unsat_prefixes.add(prefix)
                    pruned += 1
                    continue

                decisive_check = check
                break

            stats.append(
                DepthStatistics(
                    depth=depth,
                    generated=generated,
                    checked=checked,
                    pruned=pruned,
                    elapsed_seconds=perf_counter() - depth_start,
                )
            )
            if decisive_check is not None:
                status = (
                    ExplorationStatus.COUNTEREXAMPLE
                    if decisive_check.status is CheckStatus.SAT
                    else ExplorationStatus.UNKNOWN
                )
                return ExplorationResult(
                    status=status,
                    requested_upto=upto,
                    explored_upto=depth,
                    complete=False,
                    depth_statistics=tuple(stats),
                    trace_check=decisive_check,
                )

            explored_upto = depth

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
