"""Command-line interface for the Python bounded CHC explorer."""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Any

import z3

from . import __version__
from .explorer import BoundedExplorer, ExplorationResult, ExplorationStatus
from .horn import HornParseError, parse_chc_file
from .houdini import HoudiniResult, HoudiniStatus, run_seed_houdini
from .normalize import HornNormalizationError
from .solver_pool import DEFAULT_MAX_SOLVERS
from .vc import DEFAULT_MAX_SSA_CACHE_STEPS


def _non_negative_int(value: str) -> int:
    parsed = int(value)
    if parsed < 0:
        raise argparse.ArgumentTypeError("must be non-negative")
    return parsed


def _positive_int(value: str) -> int:
    parsed = int(value)
    if parsed < 1:
        raise argparse.ArgumentTypeError("must be at least 1")
    return parsed


def _ratio(value: str) -> float:
    parsed = float(value)
    if not 0.0 <= parsed <= 1.0:
        raise argparse.ArgumentTypeError("must be between 0 and 1")
    return parsed


def _parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        prog="chc-bounded-explorer",
        description=(
            "Explore bounded linear-CHC traces or run seed mining followed by "
            "multi-predicate Houdini filtering with Z3."
        ),
    )
    parser.add_argument("--version", action="version", version=__version__)
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
        type=_positive_int,
        default=1,
        help="first trace length (default: 1)",
    )
    parser.add_argument(
        "--upto",
        type=_positive_int,
        default=10_000,
        help="maximum trace length (default: 10000)",
    )
    parser.add_argument(
        "--to",
        dest="timeout_ms",
        type=_non_negative_int,
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
        "--dump-smt",
        dest="dump_smt",
        type=Path,
        help=(
            "write every checked trace as a bnd/expl-compatible SMT-LIB2 "
            "unrolling"
        ),
    )
    parser.add_argument(
        "--model", action="store_true", help="print the Z3 model for a counterexample"
    )
    parser.add_argument(
        "--seed-houdini",
        action="store_true",
        help=(
            "mine syntactic candidates for every predicate, filter them with "
            "MultiHoudini, and report Success only if all CHCs are valid"
        ),
    )
    parser.add_argument(
        "--print-invariants",
        action="store_true",
        help="print retained candidates in --seed-houdini mode",
    )
    parser.add_argument("--random-seed", type=int, help="set Z3's SMT random seed")
    parser.add_argument(
        "--solver-mode",
        choices=("pool", "fresh"),
        default="pool",
        help=(
            "solver backend: 'pool' reuses SAT prefixes with push/pop; "
            "'fresh' creates one solver per trace and never calls push/pop "
            "(default: pool)"
        ),
    )
    parser.add_argument(
        "--solver-reuse-min-ratio",
        type=_ratio,
        default=1.0 / 3.0,
        metavar="RATIO",
        help=(
            "reuse a solver only when its common prefix is longer than this "
            "fraction of the new trace (default: 1/3)"
        ),
    )
    parser.add_argument(
        "--max-solvers",
        type=_non_negative_int,
        default=DEFAULT_MAX_SOLVERS,
        metavar="N",
        help=(
            "maximum retained solver contexts in pool mode; 0 means unlimited "
            f"(default: {DEFAULT_MAX_SOLVERS})"
        ),
    )
    parser.add_argument(
        "--max-ssa-cache-steps",
        type=_non_negative_int,
        default=DEFAULT_MAX_SSA_CACHE_STEPS,
        metavar="N",
        help=(
            "maximum cached positional SSA steps/states; 0 means unlimited "
            f"(default: {DEFAULT_MAX_SSA_CACHE_STEPS})"
        ),
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
        "solver_mode": explorer.solver_mode,
        "solver_pool": {
            "max_contexts": explorer.max_solver_contexts,
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
            "max_steps": explorer.vc_builder.max_cached_steps,
            "cached_steps": explorer.ssa_statistics.cached_steps,
            "cached_states": explorer.ssa_statistics.cached_states,
            "cache_hits": explorer.ssa_statistics.cache_hits,
            "cache_misses": explorer.ssa_statistics.cache_misses,
            "cache_evictions": explorer.ssa_statistics.cache_evictions,
        },
    }
    return json.dumps(data, indent=2, sort_keys=True)


def _print_human(result: ExplorationResult, *, show_model: bool) -> None:
    if result.status is ExplorationStatus.COUNTEREXAMPLE:
        if result.trace_check is None:
            raise RuntimeError("counterexample result has no decisive trace")
        print(f"Counterexample of length {result.explored_upto} found")
        print(
            "Trace: " + " ; ".join(rule.short() for rule in result.trace_check.vc.trace)
        )
        if show_model and result.trace_check.model is not None:
            print("Model:")
            print(result.trace_check.model)
    elif result.status is ExplorationStatus.UNKNOWN:
        if result.trace_check is None:
            raise RuntimeError("unknown result has no decisive trace")
        reason = result.trace_check.reason_unknown or "unspecified"
        print(f"unknown at length {result.explored_upto}: {reason}")
    elif result.status is ExplorationStatus.COMPLETE_SAFE:
        print("Success after complete unrolling")
    elif result.status is ExplorationStatus.EMPTY:
        print("Success: no ENTRY-to-query rules remain after slicing")
    else:
        print(f"No counterexample found up to length {result.explored_upto}")


def _relation_label(relation: z3.FuncDeclRef, variables: tuple[z3.ExprRef, ...]) -> str:
    args = ", ".join(str(variable) for variable in variables)
    return f"{relation.name()}({args})"


def _houdini_json(result: HoudiniResult) -> str:
    seeds = result.seed_result
    data = {
        "status": result.status.value,
        "seed_mining": None
        if seeds is None
        else {
            "predicates": seeds.predicate_count,
            "candidates": seeds.candidate_count,
            "rules_examined": seeds.statistics.rules_examined,
            "boolean_nodes_seen": seeds.statistics.boolean_nodes_seen,
            "projections_attempted": seeds.statistics.projections_attempted,
            "projections_rejected": seeds.statistics.projections_rejected,
            "duplicate_candidates": seeds.statistics.duplicate_candidates,
        },
        "houdini": {
            "iterations": result.statistics.iterations,
            "solver_contexts": result.statistics.solver_contexts,
            "solver_checks": result.statistics.solver_checks,
            "candidates_initial": result.statistics.candidates_initial,
            "candidates_removed": result.statistics.candidates_removed,
            "candidates_remaining": result.statistics.candidates_remaining,
            "countermodels": result.statistics.countermodels,
            "unknown_checks": result.statistics.unknown_checks,
            "certification_checks": result.statistics.certification_checks,
        },
        "invariants": {
            str(relation.name()): [candidate.sexpr() for candidate in candidates]
            for relation, candidates in result.candidates.items()
        },
        "failures": [
            {
                "rule_id": failure.rule_id,
                "rule": failure.rule,
                "reason": failure.reason,
                "model": failure.model,
            }
            for failure in result.failures
        ],
    }
    return json.dumps(data, indent=2, sort_keys=True)


def _print_houdini(
    result: HoudiniResult, *, debug: int, print_invariants: bool
) -> None:
    seeds = result.seed_result
    if seeds is not None and debug:
        print(
            f"SeedMiner: predicates={seeds.predicate_count}, "
            f"candidates={seeds.candidate_count}, "
            f"boolean-nodes={seeds.statistics.boolean_nodes_seen}, "
            f"rejected-projections={seeds.statistics.projections_rejected}"
        )
    if debug:
        stats = result.statistics
        print(
            f"MultiHoudini: iterations={stats.iterations}, "
            f"checks={stats.solver_checks}, "
            f"certification-checks={stats.certification_checks}, "
            f"countermodels={stats.countermodels}, "
            f"removed={stats.candidates_removed}, "
            f"remaining={stats.candidates_remaining}"
        )
    if print_invariants:
        for relation in sorted(result.candidates, key=lambda item: str(item.name())):
            variables = result.variables[relation]
            candidates = result.candidates[relation]
            print(_relation_label(relation, variables) + ":")
            if not candidates:
                print("  true")
            else:
                for candidate in candidates:
                    print(f"  {candidate}")
    if result.status is HoudiniStatus.SUCCESS:
        print("Success")
    else:
        print("unknown")
        if debug:
            for failure in result.failures:
                print(
                    f"  r{failure.rule_id} {failure.rule}: {failure.reason}",
                    file=sys.stderr,
                )


def main(argv: list[str] | None = None) -> int:
    parser = _parser()
    args = parser.parse_args(argv)
    if args.upto < args.start:
        parser.error("--upto must be greater than or equal to --from")
    if args.dump_smt is not None and args.dump_smt.exists():
        if not args.dump_smt.is_dir():
            parser.error("--dump-smt must name a directory")
    try:
        program = parse_chc_file(
            args.file,
            slice_program=False if args.seed_houdini else not args.skip_elim,
        )
        if args.debug:
            mode = "sliced" if program.sliced else "unsliced"
            print(
                f"Parsed {len(program.rules)} linear CHCs ({mode}); Z3 {z3.get_version_string()}"
            )
            for rule in program.rules:
                print(f"  {rule.short()}: {rule.body}")

        if args.seed_houdini:
            houdini_result = run_seed_houdini(
                program,
                timeout_ms=args.timeout_ms,
                random_seed=args.random_seed,
            )
            if args.json:
                print(_houdini_json(houdini_result))
            else:
                _print_houdini(
                    houdini_result,
                    debug=args.debug,
                    print_invariants=args.print_invariants,
                )
            return 0 if houdini_result.status is HoudiniStatus.SUCCESS else 2

        explorer = BoundedExplorer(
            program,
            timeout_ms=args.timeout_ms,
            random_seed=args.random_seed,
            smt_dump_dir=args.dump_smt,
            solver_mode=args.solver_mode,
            solver_reuse_min_ratio=args.solver_reuse_min_ratio,
            max_solver_contexts=(None if args.max_solvers == 0 else args.max_solvers),
            max_cached_ssa_steps=(
                None if args.max_ssa_cache_steps == 0 else args.max_ssa_cache_steps
            ),
        )
        result = explorer.explore(start=args.start, upto=args.upto)

        if args.debug:
            for item in result.depth_statistics:
                print(
                    f"depth {item.depth}: generated={item.generated}, "
                    f"checked={item.checked}, learned-unsat-prefixes={item.pruned}, "
                    f"time={item.elapsed_seconds:.6f}s"
                )
            pool = explorer.solver_statistics
            ssa = explorer.ssa_statistics
            print(
                f"solver ({explorer.solver_mode}): "
                f"limit={explorer.max_solver_contexts}, contexts={pool.contexts}, "
                f"created={pool.solvers_created}, "
                f"recycled={pool.contexts_recycled}, reused={pool.traces_reused}, "
                f"reused-prefix-steps={pool.common_prefix_steps_reused}, "
                f"pushes={pool.pushes}, pops={pool.pops}, checks={pool.checks}"
            )
            print(
                "SSA cache: "
                f"limit={explorer.vc_builder.max_cached_steps}, "
                f"steps={ssa.cached_steps}, states={ssa.cached_states}, "
                f"hits={ssa.cache_hits}, misses={ssa.cache_misses}, "
                f"evictions={ssa.cache_evictions}"
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

        if result.status is ExplorationStatus.COUNTEREXAMPLE:
            return 1
        if result.status is ExplorationStatus.UNKNOWN:
            return 2
        return 0
    except (HornParseError, HornNormalizationError, OSError) as exc:
        print(f"error: {exc}", file=sys.stderr)
        return 3


if __name__ == "__main__":
    raise SystemExit(main())
