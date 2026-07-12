"""Command-line interface for the Python bounded CHC explorer."""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Any

import z3

from .explorer import BoundedExplorer, ExplorationResult, ExplorationStatus
from .horn import HornParseError, parse_chc_file
from .normalize import HornNormalizationError


def _parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        prog="chc-bounded-explorer",
        description=(
            "Exhaustively enumerate increasing-size linear-CHC unrollings and "
            "check their verification conditions with Z3."
        ),
    )
    parser.add_argument(
        "file",
        type=Path,
        help=(
            "linear CHC file in rule/query syntax or pure SMT-LIB assert/forall syntax"
        ),
    )
    parser.add_argument(
        "--from",
        dest="start",
        type=int,
        default=1,
        help="first trace length (default: 1)",
    )
    parser.add_argument(
        "--upto", type=int, default=10_000, help="maximum trace length (default: 10000)"
    )
    parser.add_argument(
        "--to",
        dest="timeout_ms",
        type=int,
        default=1_000,
        help="timeout for each Z3 check in ms (default: 1000)",
    )
    parser.add_argument(
        "--skip-elim",
        action="store_true",
        help="compatibility option: retain rules outside ENTRY-to-query slices",
    )
    parser.add_argument(
        "--debug",
        action="count",
        default=0,
        help="print normalized rules and per-depth statistics",
    )
    parser.add_argument(
        "--json", action="store_true", help="emit a machine-readable JSON result"
    )
    parser.add_argument(
        "--dump-vc",
        type=Path,
        help="write the decisive SAT/unknown verification condition as SMT-LIB2",
    )
    parser.add_argument(
        "--dump-ssa",
        "--dump-ssa-dir",
        dest="dump_ssa",
        type=Path,
        help=(
            "write every constructed trace SSA to a separate SMT-LIB2 file in "
            "an empty directory"
        ),
    )
    parser.add_argument(
        "--model", action="store_true", help="print the Z3 model for a counterexample"
    )
    parser.add_argument("--random-seed", type=int, help="set Z3's SMT random seed")
    parser.add_argument(
        "--fresh-solvers",
        action="store_true",
        help="disable longest-common-prefix solver reuse for comparison",
    )
    parser.add_argument(
        "--solver-reuse-min-ratio",
        type=float,
        default=1.0 / 3.0,
        metavar="RATIO",
        help=(
            "reuse a solver only when its common prefix is longer than this "
            "fraction of the new trace (default: 1/3)"
        ),
    )
    parser.add_argument(
        "--max-solvers",
        type=int,
        default=0,
        metavar="N",
        help="maximum retained solver contexts; 0 means unlimited (default: 0)",
    )
    return parser


def _trace_data(result: ExplorationResult) -> dict[str, Any] | None:
    check = result.trace_check
    if check is None:
        return None
    return {
        "status": check.status.value,
        "rule_ids": list(check.vc.rule_ids),
        "rules": [rule.short() for rule in check.vc.trace],
        "elapsed_seconds": check.elapsed_seconds,
        "unsat_prefix_length": check.unsat_prefix_length,
        "reason_unknown": check.reason_unknown,
        "model": None if check.model is None else str(check.model),
    }


def _as_json(
    result: ExplorationResult, program_rules: int, explorer: BoundedExplorer
) -> str:
    data = {
        "status": result.status.value,
        "requested_upto": result.requested_upto,
        "explored_upto": result.explored_upto,
        "complete": result.complete,
        "rules": program_rules,
        "depths": [
            {
                "depth": item.depth,
                "generated": item.generated,
                "checked": item.checked,
                "pruned": item.pruned,
                "elapsed_seconds": item.elapsed_seconds,
            }
            for item in result.depth_statistics
        ],
        "decisive_trace": _trace_data(result),
        "solver_pool": {
            "contexts": explorer.solver_statistics.contexts,
            "solvers_created": explorer.solver_statistics.solvers_created,
            "contexts_recycled": explorer.solver_statistics.contexts_recycled,
            "traces_reused": explorer.solver_statistics.traces_reused,
            "exact_prefix_hits": explorer.solver_statistics.exact_prefix_hits,
            "common_prefix_steps_reused": (
                explorer.solver_statistics.common_prefix_steps_reused
            ),
            "pushes": explorer.solver_statistics.pushes,
            "pops": explorer.solver_statistics.pops,
            "checks": explorer.solver_statistics.checks,
        },
        "ssa_cache": {
            "cached_steps": explorer.ssa_statistics.cached_steps,
            "cache_hits": explorer.ssa_statistics.cache_hits,
            "cache_misses": explorer.ssa_statistics.cache_misses,
        },
    }
    return json.dumps(data, indent=2, sort_keys=True)


def _print_human(result: ExplorationResult, *, show_model: bool) -> None:
    if result.status is ExplorationStatus.COUNTEREXAMPLE:
        assert result.trace_check is not None
        print(f"Counterexample of length {result.explored_upto} found")
        print(
            "Trace: " + " ; ".join(rule.short() for rule in result.trace_check.vc.trace)
        )
        if show_model and result.trace_check.model is not None:
            print("Model:")
            print(result.trace_check.model)
    elif result.status is ExplorationStatus.UNKNOWN:
        assert result.trace_check is not None
        reason = result.trace_check.reason_unknown or "unspecified"
        print(f"unknown at length {result.explored_upto}: {reason}")
    elif result.status is ExplorationStatus.COMPLETE_SAFE:
        print("Success after complete unrolling")
    elif result.status is ExplorationStatus.EMPTY:
        print("Success: no ENTRY-to-query rules remain after slicing")
    else:
        print(f"No counterexample found up to length {result.explored_upto}")


def main(argv: list[str] | None = None) -> int:
    args = _parser().parse_args(argv)
    try:
        program = parse_chc_file(args.file, slice_program=not args.skip_elim)
        if args.debug:
            mode = "sliced" if program.sliced else "unsliced"
            print(
                f"Parsed {len(program.rules)} linear CHCs ({mode}); Z3 {z3.get_version_string()}"
            )
            for rule in program.rules:
                print(f"  {rule.short()}: {rule.body}")

        explorer = BoundedExplorer(
            program,
            timeout_ms=args.timeout_ms,
            random_seed=args.random_seed,
            ssa_dump_dir=args.dump_ssa,
            use_solver_pool=not args.fresh_solvers,
            solver_reuse_min_ratio=args.solver_reuse_min_ratio,
            max_solver_contexts=(None if args.max_solvers == 0 else args.max_solvers),
        )
        result = explorer.explore(start=args.start, upto=args.upto)

        if args.debug:
            for item in result.depth_statistics:
                print(
                    f"depth {item.depth}: generated={item.generated}, "
                    f"checked={item.checked}, learned-unsat-prefixes={item.pruned}, "
                    f"time={item.elapsed_seconds:.6f}s"
                )
        if args.debug:
            pool = explorer.solver_statistics
            ssa = explorer.ssa_statistics
            print(
                "solver pool: "
                f"contexts={pool.contexts}, created={pool.solvers_created}, "
                f"reused={pool.traces_reused}, "
                f"reused-prefix-steps={pool.common_prefix_steps_reused}, "
                f"pushes={pool.pushes}, pops={pool.pops}, checks={pool.checks}"
            )
            print(
                "SSA cache: "
                f"steps={ssa.cached_steps}, hits={ssa.cache_hits}, "
                f"misses={ssa.cache_misses}"
            )
        if args.json:
            print(_as_json(result, len(program.rules), explorer))
        else:
            _print_human(result, show_model=args.model)

        if args.dump_vc is not None:
            if result.trace_check is None:
                print(
                    "--dump-vc requested, but no decisive trace exists", file=sys.stderr
                )
            else:
                args.dump_vc.write_text(
                    result.trace_check.vc.to_smt2(), encoding="utf-8"
                )

        if args.dump_ssa is not None:
            print(
                f"Dumped {explorer.ssa_dump_count} SSA verification condition(s) "
                f"to {explorer.ssa_dump_dir}",
                file=sys.stderr,
            )

        if result.status is ExplorationStatus.COUNTEREXAMPLE:
            return 1
        if result.status is ExplorationStatus.UNKNOWN:
            return 2
        return 0
    except (HornParseError, HornNormalizationError, ValueError, OSError) as exc:
        print(f"error: {exc}", file=sys.stderr)
        return 3


if __name__ == "__main__":
    raise SystemExit(main())
