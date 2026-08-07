"""Command-line interface for the Python bounded CHC explorer."""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Any

import z3

from . import __version__
from .candidate_validation import (
    DEFAULT_CANDIDATE_BOUND,
    CandidateReachability,
    CandidateValidation,
    dump_promising_candidate_files,
    validate_removed_candidate,
)
from .cands import format_candidates_smt2, merge_candidate_maps, parse_candidate_file
from .explorer import BoundedExplorer, ExplorationResult, ExplorationStatus
from .horn import HornParseError, parse_chc_file
from .houdini import HoudiniResult, HoudiniStatus, MultiHoudini, RemovedCandidate
from .normalize import HornNormalizationError
from .seedminer import CandidateMap, SeedMiner
from .solver_pool import DEFAULT_MAX_SOLVERS
from .vc import DEFAULT_MAX_SSA_CACHE_STEPS, VerificationConditionBuilder


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
        "--cands",
        type=Path,
        metavar="FILE",
        help=(
            "SMT-LIB2 file of define-fun invariant candidates, one define-fun "
            "per uninterpreted predicate. Implies Houdini mode: each body is "
            "parsed, its parameters are renamed to the predicate's canonical "
            "variables, the result is split into conjuncts, and MultiHoudini "
            "iteratively removes conjuncts until the remainder is inductive. "
            "May be combined with --seed-houdini to merge user-supplied and "
            "mined candidates before filtering."
        ),
    )
    parser.add_argument(
        "--print-invariants",
        action="store_true",
        help="print retained candidates in --seed-houdini / --cands mode",
    )
    parser.add_argument(
        "--dump-cands",
        type=Path,
        metavar="FILE",
        help=(
            "write the retained candidates from --seed-houdini / --cands "
            "mode as an SMT-LIB2 define-fun file that --cands can read back "
            "(unlike --print-invariants, which prints Python infix notation "
            "and is not valid SMT-LIB2). Written regardless of the final "
            "status, so it also captures a partial/insufficient candidate "
            "set for later inspection. Requires --seed-houdini or --cands."
        ),
    )
    parser.add_argument(
        "--validate-candidates",
        action="store_true",
        help=(
            "for each candidate MultiHoudini removes, bound-check whether "
            "it is actually falsifiable by unrolling the program from ENTRY "
            "(see --candidate-bound). Confirms real removals and flags ones "
            "with no falsifying state found within the bound as potentially "
            "promising candidates that may need a helper lemma. Shown in "
            "--debug output and always included in --json output when set. "
            "Requires --seed-houdini or --cands."
        ),
    )
    parser.add_argument(
        "--candidate-bound",
        type=int,
        default=DEFAULT_CANDIDATE_BOUND,
        metavar="N",
        help=(
            f"max unrolling depth for --validate-candidates (default: "
            f"{DEFAULT_CANDIDATE_BOUND})"
        ),
    )
    parser.add_argument(
        "--dump-promising-candidates",
        type=Path,
        metavar="DIR",
        help=(
            "for each candidate --validate-candidates flags as potentially "
            "promising (not-found), write a standalone SMT-LIB2 file to DIR "
            "(created if missing) that reuses every rule of the original "
            "program but replaces the safety property with a direct check "
            "of whether that candidate holds for its relation -- an "
            "independently checkable question, e.g. by re-running "
            "chc-bounded-explorer on it with a larger --upto or "
            "--seed-houdini, or by handing it to any other HORN-capable "
            "solver. Requires --validate-candidates."
        ),
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


def _format_candidate_verdict(v: CandidateValidation) -> str:
    if v.status is CandidateReachability.REACHABLE:
        return f"confirmed real (falsified by a reachable state at depth {v.witness_depth})"
    if v.status is CandidateReachability.NOT_FOUND:
        return (
            f"potentially promising (no falsifying state found within "
            f"{v.checked_upto} steps -- may need a helper lemma)"
        )
    if v.status is CandidateReachability.UNKNOWN:
        reason = v.reason_unknown or "unspecified"
        return f"inconclusive (Z3 returned unknown while checking: {reason})"
    return "confirmed real (base case, always reachable)"


def _format_removed_candidate(
    rc: RemovedCandidate,
    verdict: CandidateValidation | None = None,
    verification_file: Path | None = None,
) -> str:
    """Human-readable summary of one candidate dropped by Houdini filtering."""
    lines = [f"  dropped r{rc.rule_id}[{rc.rule}] {rc.relation}: {rc.candidate}"]
    if rc.pre_state is not None:
        lines.append(f"    pre:  {rc.pre_state}")
    else:
        lines.append("    pre:  (fact -- no source predicate)")
    lines.append(f"    post: {rc.post_state}")
    if verdict is not None:
        lines.append(f"    check: {_format_candidate_verdict(verdict)}")
    if verification_file is not None:
        lines.append(f"    file: {verification_file}")
    return "\n".join(lines)


def _houdini_json(
    result: HoudiniResult,
    *,
    user_candidates: CandidateMap | None,
    candidate_validations: tuple[CandidateValidation, ...] | None = None,
    candidate_files_by_index: dict[int, Path] | None = None,
) -> str:
    seeds = result.seed_result
    validation_by_index: tuple[CandidateValidation | None, ...] = (
        candidate_validations
        if candidate_validations is not None
        else (None,) * len(result.removed_candidates)
    )
    files_by_index = candidate_files_by_index or {}
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
        "user_candidates": None
        if user_candidates is None
        else {
            "predicates": len(user_candidates),
            "candidates": sum(len(items) for items in user_candidates.values()),
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
        "removed_candidates": [
            {
                "relation": rc.relation,
                "candidate": rc.candidate,
                "rule_id": rc.rule_id,
                "rule": rc.rule,
                "pre_state": rc.pre_state,
                "post_state": rc.post_state,
                "full_model": rc.full_model,
                "candidate_validation": None
                if verdict is None
                else {
                    "status": verdict.status.value,
                    "checked_upto": verdict.checked_upto,
                    "witness_depth": verdict.witness_depth,
                    "checks_performed": verdict.checks_performed,
                    "elapsed_seconds": verdict.elapsed_seconds,
                    "reason_unknown": verdict.reason_unknown,
                },
                "verification_file": str(files_by_index[index])
                if index in files_by_index
                else None,
            }
            for index, (rc, verdict) in enumerate(
                zip(result.removed_candidates, validation_by_index, strict=True)
            )
        ],
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
    result: HoudiniResult,
    *,
    debug: int,
    print_invariants: bool,
    user_candidates: CandidateMap | None = None,
    candidate_validations: tuple[CandidateValidation, ...] | None = None,
    candidate_files_by_index: dict[int, Path] | None = None,
) -> None:
    seeds = result.seed_result
    if seeds is not None and debug:
        print(
            f"SeedMiner: predicates={seeds.predicate_count}, "
            f"candidates={seeds.candidate_count}, "
            f"boolean-nodes={seeds.statistics.boolean_nodes_seen}, "
            f"rejected-projections={seeds.statistics.projections_rejected}"
        )
    if user_candidates is not None and debug:
        print(
            f"Cands: predicates={len(user_candidates)}, "
            f"candidates={sum(len(items) for items in user_candidates.values())}"
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
    if debug and result.removed_candidates:
        print(
            f"Dropped candidates ({len(result.removed_candidates)}):",
            file=sys.stderr,
        )
        validation_by_index: tuple[CandidateValidation | None, ...] = (
            candidate_validations
            if candidate_validations is not None
            else (None,) * len(result.removed_candidates)
        )
        files_by_index = candidate_files_by_index or {}
        for index, (rc, verdict) in enumerate(
            zip(result.removed_candidates, validation_by_index, strict=True)
        ):
            print(
                _format_removed_candidate(rc, verdict, files_by_index.get(index)),
                file=sys.stderr,
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
    if args.dump_cands is not None and not (
        args.seed_houdini or args.cands is not None
    ):
        parser.error("--dump-cands requires --seed-houdini or --cands")
    if args.validate_candidates and not (args.seed_houdini or args.cands is not None):
        parser.error("--validate-candidates requires --seed-houdini or --cands")
    if args.candidate_bound < 1:
        parser.error("--candidate-bound must be at least 1")
    if args.dump_promising_candidates is not None and not args.validate_candidates:
        parser.error("--dump-promising-candidates requires --validate-candidates")
    try:
        # Disable program slicing when running in Houdini mode: the full set
        # of relations (including any outside the ENTRY-to-query slice) may
        # be relevant to invariants that are mined or user-supplied.
        houdini_mode = args.seed_houdini or args.cands is not None
        program = parse_chc_file(
            args.file,
            slice_program=False if houdini_mode else not args.skip_elim,
        )
        if args.debug:
            mode = "sliced" if program.sliced else "unsliced"
            arithmetic = program.arithmetic_sorts
            numeric = (
                "mixed Int/Real"
                if arithmetic.is_mixed
                else "Real"
                if arithmetic.uses_real
                else "Int"
                if arithmetic.uses_integer
                else "non-arithmetic"
            )
            theories = [numeric]
            if program.string_sorts.uses_string:
                theories.append(
                    "String+RegEx"
                    if program.string_sorts.uses_regular_expressions
                    else "String"
                )
            print(
                f"Parsed {len(program.rules)} linear CHCs "
                f"({mode}, {', '.join(theories)}); "
                f"Z3 {z3.get_version_string()}"
            )
            for rule in program.rules:
                print(f"  {rule.short()}: {rule.body}")

        if houdini_mode:
            # SeedMiner allocates the canonical VariableMap in __init__,
            # independent of the candidate-mining pass performed by .mine().
            # Only run .mine() when --seed-houdini was requested, so a plain
            # --cands run does not pay for syntactic candidate mining it
            # will not use.
            miner = SeedMiner(program)
            seed_result = miner.mine() if args.seed_houdini else None
            candidates: CandidateMap = (
                {} if seed_result is None else seed_result.candidates
            )

            user_candidates: CandidateMap | None = None
            if args.cands is not None:
                user_candidates = parse_candidate_file(args.cands, miner.variables)
                candidates = merge_candidate_maps(candidates, user_candidates)

            houdini_result = MultiHoudini(
                program,
                miner.variables,
                timeout_ms=args.timeout_ms,
                random_seed=args.random_seed,
            ).run(candidates, seed_result=seed_result)

            candidate_validations: tuple[CandidateValidation, ...] | None = None
            candidate_files_by_index: dict[int, Path] = {}
            if args.validate_candidates:
                # A shared VerificationConditionBuilder lets validations for
                # different removed candidates reuse each other's SSA step
                # construction for any prefixes they have in common.
                vc_builder = VerificationConditionBuilder(program)
                candidate_validations = tuple(
                    validate_removed_candidate(
                        program,
                        houdini_result.variables,
                        rc,
                        upto=args.candidate_bound,
                        timeout_ms=args.timeout_ms,
                        builder=vc_builder,
                    )
                    for rc in houdini_result.removed_candidates
                )
                if args.dump_promising_candidates is not None:
                    candidate_files_by_index = dump_promising_candidate_files(
                        program,
                        houdini_result.variables,
                        houdini_result.removed_candidates,
                        candidate_validations,
                        args.dump_promising_candidates,
                    )
                    if args.debug:
                        print(
                            f"Validation: wrote {len(candidate_files_by_index)} "
                            "potentially-promising verification file(s) to "
                            f"{args.dump_promising_candidates}"
                        )

            if args.dump_cands is not None:
                header = (
                    f"Retained candidates from {args.file}\n"
                    f"status: {houdini_result.status.value}\n"
                    f"source: "
                    + (
                        "--seed-houdini"
                        + (" + --cands " + str(args.cands) if args.cands else "")
                        if args.seed_houdini
                        else "--cands " + str(args.cands)
                    )
                    + "\n"
                    "Machine-generated by chc-bounded-explorer --dump-cands; "
                    "readable by --cands."
                )
                dump_text = format_candidates_smt2(
                    houdini_result.candidates, houdini_result.variables, header=header
                )
                args.dump_cands.write_text(dump_text, encoding="utf-8")
                if args.debug:
                    print(f"Cands: wrote {args.dump_cands}")

            if args.json:
                print(
                    _houdini_json(
                        houdini_result,
                        user_candidates=user_candidates,
                        candidate_validations=candidate_validations,
                        candidate_files_by_index=candidate_files_by_index,
                    )
                )
            else:
                _print_houdini(
                    houdini_result,
                    debug=args.debug,
                    print_invariants=args.print_invariants,
                    user_candidates=user_candidates,
                    candidate_validations=candidate_validations,
                    candidate_files_by_index=candidate_files_by_index,
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
