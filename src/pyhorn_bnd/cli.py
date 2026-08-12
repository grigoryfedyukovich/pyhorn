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
from .houdini import (
    HoudiniResult,
    HoudiniStatus,
    MultiHoudini,
    RemovedCandidate,
    run_trace_houdini,
)
from .normalize import HornNormalizationError
from .seedminer import (
    DEFAULT_MAX_EQUALITY_SUBSTITUTIONS_PER_RELATION,
    DEFAULT_MAX_MUTATION_TERMS_PER_RELATION,
    CandidateMap,
    MutationResult,
    SeedMiner,
    mutate_candidates,
)
from .solver_pool import DEFAULT_MAX_SOLVERS
from .trace_miner import (
    DEFAULT_MODELS_PER_PREFIX,
    DEFAULT_SAMPLES_PER_RELATION,
    DEFAULT_TRACE_CANDIDATES_PER_RELATION,
    DEFAULT_TRACE_DEPTH,
    DEFAULT_TRACE_LIMIT,
    trace_template_specifications,
)
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
        nargs="?",
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
        help="print retained candidates in --seed-houdini / --cands / --trace-houdini mode",
    )
    parser.add_argument(
        "--mut",
        action="store_true",
        help=(
            "before running MultiHoudini, derive additional candidates by "
            "combining pairs of existing numeric equalities and "
            "inequalities within each relation's pool (e.g. x<=y and "
            "y<=z produce x<=z; x=a and y=b also produce x+y=a+b and "
            "x-y=a-b). Applies to the full combined candidate set from "
            "whichever of --seed-houdini, --cands, and --trace-houdini "
            "were used. Requires one of those three."
        ),
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
    parser.add_argument(
        "--trace-houdini",
        action="store_true",
        help=(
            "run staged trace-guided synthesis: try ordinary --seed-houdini "
            "first, and only if that does not prove the program, sample "
            "concrete bounded reachable-state models and generalize them "
            "into additional invariant-candidate templates, then retry "
            "MultiHoudini with the combined candidate set. Monotonic with "
            "respect to plain --seed-houdini: if the syntactic baseline "
            "already succeeds, trace sampling is skipped entirely. "
            "--seed-houdini may be passed alongside it but has no separate "
            "effect, since this pipeline already performs that attempt as "
            "its own first stage. Combinable with --mut (applied at every "
            "stage of this pipeline); a separate mode from --cands in this "
            "release -- not yet combinable with --cands, "
            "--validate-candidates, --dump-cands, or "
            "--dump-promising-candidates."
        ),
    )
    parser.add_argument(
        "--trace-depth",
        type=_positive_int,
        default=DEFAULT_TRACE_DEPTH,
        metavar="N",
        help=(
            f"maximum sampled prefix depth for --trace-houdini (default: "
            f"{DEFAULT_TRACE_DEPTH})"
        ),
    )
    parser.add_argument(
        "--trace-limit",
        type=_positive_int,
        default=DEFAULT_TRACE_LIMIT,
        metavar="N",
        help=(
            f"maximum sampled prefixes for --trace-houdini (default: "
            f"{DEFAULT_TRACE_LIMIT})"
        ),
    )
    parser.add_argument(
        "--trace-models-per-prefix",
        type=_positive_int,
        default=DEFAULT_MODELS_PER_PREFIX,
        metavar="N",
        help=(
            "maximum distinct destination models sampled per prefix "
            f"(default: {DEFAULT_MODELS_PER_PREFIX})"
        ),
    )
    parser.add_argument(
        "--trace-samples-per-predicate",
        type=_positive_int,
        default=DEFAULT_SAMPLES_PER_RELATION,
        metavar="N",
        help=(
            "maximum concrete states retained per predicate "
            f"(default: {DEFAULT_SAMPLES_PER_RELATION})"
        ),
    )
    parser.add_argument(
        "--trace-candidates-per-predicate",
        type=_positive_int,
        default=DEFAULT_TRACE_CANDIDATES_PER_RELATION,
        metavar="N",
        help=(
            "maximum trace-generalized candidates per predicate "
            f"(default: {DEFAULT_TRACE_CANDIDATES_PER_RELATION})"
        ),
    )
    parser.add_argument(
        "--trace-mutation-limit",
        type=_non_negative_int,
        default=DEFAULT_MAX_MUTATION_TERMS_PER_RELATION,
        metavar="N",
        help=(
            "with --trace-houdini --mut, cap how many equalities and how "
            "many inequalities (independently) are drawn from each "
            "predicate's candidate pool before --mut pairs them up "
            "(numeric +/- combination and inequality chaining), and how "
            "many equalities of any sort feed sort-agnostic equality "
            "substitution; 0 means unlimited. Pairing cost is quadratic in "
            "this count, and trace-sampled pools can carry far more "
            "equalities than syntactically-mined ones, so the default "
            f"keeps --mut tractable on them (default: "
            f"{DEFAULT_MAX_MUTATION_TERMS_PER_RELATION})"
        ),
    )
    parser.add_argument(
        "--trace-mutation-substitution-limit",
        type=_non_negative_int,
        default=DEFAULT_MAX_EQUALITY_SUBSTITUTIONS_PER_RELATION,
        metavar="N",
        help=(
            "with --trace-houdini --mut, cap how many equality-substitution "
            "rewrite attempts (any sort -- String, Array, Bool, not just "
            "arithmetic) are made per predicate; 0 means unlimited. A "
            "separate knob from --trace-mutation-limit: substitution's cost "
            "profile (candidates rewritten x equalities used as rewrite "
            "rules) is independent of numeric pairing's "
            f"(default: {DEFAULT_MAX_EQUALITY_SUBSTITUTIONS_PER_RELATION})"
        ),
    )
    parser.add_argument(
        "--list-trace-templates",
        action="store_true",
        help=(
            "print the complete stable registry of trace-generalization "
            "templates used by --trace-houdini and exit; does not require "
            "the file argument. Combine with --json for machine-readable "
            "output."
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
    mutation_result: MutationResult | None = None,
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
        "mutation": None
        if mutation_result is None
        else {
            "equalities_considered": mutation_result.statistics.equalities_considered,
            "inequalities_considered": (
                mutation_result.statistics.inequalities_considered
            ),
            "equality_pairs_combined": (
                mutation_result.statistics.equality_pairs_combined
            ),
            "inequality_chains_combined": (
                mutation_result.statistics.inequality_chains_combined
            ),
            "candidates_added": mutation_result.statistics.candidates_added,
            "terms_dropped_by_cap": (
                mutation_result.statistics.terms_dropped_by_cap
            ),
            "general_equalities_considered": (
                mutation_result.statistics.general_equalities_considered
            ),
            "substitution_rewrites_attempted": (
                mutation_result.statistics.substitution_rewrites_attempted
            ),
            "substitution_candidates_added": (
                mutation_result.statistics.substitution_candidates_added
            ),
            "substitutions_dropped_by_cap": (
                mutation_result.statistics.substitutions_dropped_by_cap
            ),
            "string_bridges_emitted": (
                mutation_result.statistics.string_bridges_emitted
            ),
            "regex_memberships_considered": (
                mutation_result.statistics.regex_memberships_considered
            ),
            "regex_pairs_intersected": (
                mutation_result.statistics.regex_pairs_intersected
            ),
        },
        "trace_mining": None
        if result.trace_result is None
        else {
            "max_depth": result.trace_result.statistics.max_depth,
            "prefixes_checked": result.trace_result.statistics.prefixes_checked,
            "sat_prefixes": result.trace_result.statistics.sat_prefixes,
            "unsat_prefixes": result.trace_result.statistics.unsat_prefixes,
            "unknown_prefixes": result.trace_result.statistics.unknown_prefixes,
            "models_extracted": result.trace_result.statistics.models_extracted,
            "duplicate_samples": result.trace_result.statistics.duplicate_samples,
            "sample_limit_hits": result.trace_result.statistics.sample_limit_hits,
            "candidate_limit_hits": (
                result.trace_result.statistics.candidate_limit_hits
            ),
            "candidates": result.trace_result.statistics.candidates_mined,
            "template_counts": {
                template_id: sum(
                    1
                    for item in result.trace_result.observations
                    if item.template_id.value == template_id
                )
                for template_id in sorted(
                    {
                        item.template_id.value
                        for item in result.trace_result.observations
                    }
                )
            },
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
    mutation_result: MutationResult | None = None,
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
    if mutation_result is not None and debug:
        stats = mutation_result.statistics
        capped = (
            f", capped={stats.terms_dropped_by_cap}"
            if stats.terms_dropped_by_cap
            else ""
        )
        print(
            f"Mutation: equalities={stats.equalities_considered}, "
            f"inequalities={stats.inequalities_considered}, "
            f"eq-pairs={stats.equality_pairs_combined}, "
            f"ineq-chains={stats.inequality_chains_combined}, "
            f"added={stats.candidates_added}{capped}"
        )
        # Sort-agnostic substitution, explicit String bridges, and regex
        # intersection are separate mechanisms from the numeric pairing
        # above (see mutate_candidates()'s docstring); only printed when
        # at least one actually had something to do, so a purely-numeric
        # benchmark's --debug output doesn't grow a second line of zeros.
        if (
            stats.general_equalities_considered
            or stats.string_bridges_emitted
            or stats.regex_memberships_considered
        ):
            sub_capped = (
                f", sub-capped={stats.substitutions_dropped_by_cap}"
                if stats.substitutions_dropped_by_cap
                else ""
            )
            print(
                f"Mutation (bridges): general-equalities="
                f"{stats.general_equalities_considered}, "
                f"substitutions-attempted={stats.substitution_rewrites_attempted}, "
                f"substitutions-added={stats.substitution_candidates_added}, "
                f"string-bridges={stats.string_bridges_emitted}, "
                f"regex-memberships={stats.regex_memberships_considered}, "
                f"regex-pairs={stats.regex_pairs_intersected}{sub_capped}"
            )
    if result.trace_result is not None and debug:
        trace_stats = result.trace_result.statistics
        print(
            f"TraceMiner: depth={trace_stats.max_depth}, "
            f"prefixes={trace_stats.prefixes_checked}, "
            f"sat={trace_stats.sat_prefixes}, "
            f"models={trace_stats.models_extracted}, "
            f"candidates={trace_stats.candidates_mined}, "
            f"unknown={trace_stats.unknown_prefixes}"
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


def _print_trace_template_registry(*, as_json: bool) -> None:
    specifications = trace_template_specifications()
    if as_json:
        print(
            json.dumps(
                [
                    {
                        "id": item.template_id.value,
                        "domain": item.domain,
                        "formula_schema": item.formula_schema,
                        "applicable_features": list(item.applicable_features),
                        "emission_condition": item.emission_condition,
                    }
                    for item in specifications
                ],
                indent=2,
                sort_keys=True,
            )
        )
        return
    for item in specifications:
        print(item.template_id.value)
        print(f"  domain: {item.domain}")
        print(f"  formula: {item.formula_schema}")
        print("  features: " + "; ".join(item.applicable_features))
        print(f"  emit when: {item.emission_condition}")


def main(argv: list[str] | None = None) -> int:
    parser = _parser()
    args = parser.parse_args(argv)
    if args.list_trace_templates:
        _print_trace_template_registry(as_json=args.json)
        return 0
    if args.file is None:
        parser.error("the following arguments are required: file")
    if args.upto < args.start:
        parser.error("--upto must be greater than or equal to --from")
    if (
        args.dump_smt is not None
        and args.dump_smt.exists()
        and not args.dump_smt.is_dir()
    ):
        parser.error("--dump-smt must name a directory")
    # --seed-houdini is deliberately NOT rejected in combination with
    # --trace-houdini: run_trace_houdini() already performs an ordinary
    # seed-houdini attempt as its own first stage, so passing --seed-houdini
    # alongside it is accepted as a (redundant but harmless) no-op rather
    # than an error.
    if args.trace_houdini and args.cands is not None:
        parser.error("--trace-houdini cannot be combined with --cands")
    if args.trace_houdini and args.validate_candidates:
        parser.error("--trace-houdini cannot be combined with --validate-candidates")
    if args.trace_houdini and args.dump_cands is not None:
        parser.error("--trace-houdini cannot be combined with --dump-cands")
    if args.dump_cands is not None and not (
        args.seed_houdini or args.cands is not None
    ):
        parser.error("--dump-cands requires --seed-houdini or --cands")
    if args.validate_candidates and not (args.seed_houdini or args.cands is not None):
        parser.error("--validate-candidates requires --seed-houdini or --cands")
    if args.mut and not (
        args.seed_houdini or args.cands is not None or args.trace_houdini
    ):
        parser.error("--mut requires --seed-houdini, --cands, or --trace-houdini")
    if args.candidate_bound < 1:
        parser.error("--candidate-bound must be at least 1")
    if args.dump_promising_candidates is not None and not args.validate_candidates:
        parser.error("--dump-promising-candidates requires --validate-candidates")
    try:
        # Disable program slicing when running in Houdini mode: the full set
        # of relations (including any outside the ENTRY-to-query slice) may
        # be relevant to invariants that are mined or user-supplied.
        houdini_mode = (
            args.seed_houdini or args.cands is not None or args.trace_houdini
        )
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
                string_features = ["String"]
                if program.string_sorts.uses_regular_expressions:
                    string_features.append("RegEx")
                if program.string_sorts.uses_length_constraints:
                    string_features.append("Length")
                theories.append("+".join(string_features))
            print(
                f"Parsed {len(program.rules)} linear CHCs "
                f"({mode}, {', '.join(theories)}); "
                f"Z3 {z3.get_version_string()}"
            )
            for rule in program.rules:
                print(f"  {rule.short()}: {rule.body}")

        if houdini_mode:
            user_candidates: CandidateMap | None = None
            mutation_result: MutationResult | None = None
            if args.trace_houdini:
                # A separate top-level pipeline from the accumulate-then-run
                # flow below: run_trace_houdini stages its own baseline
                # seed-houdini attempt internally (so a redundant
                # --seed-houdini alongside it, permitted above, has no
                # separate effect here) and only spends the trace-sampling
                # budget if that fails, so there is nothing here to merge
                # with --cands (disallowed above). --mut is supported
                # directly by run_trace_houdini, which applies it to the
                # candidate set live at each of its own stages.
                houdini_result = run_trace_houdini(
                    program,
                    trace_depth=args.trace_depth,
                    trace_limit=args.trace_limit,
                    models_per_prefix=args.trace_models_per_prefix,
                    max_samples_per_relation=args.trace_samples_per_predicate,
                    max_trace_candidates_per_relation=(
                        args.trace_candidates_per_predicate
                    ),
                    timeout_ms=args.timeout_ms,
                    random_seed=args.random_seed,
                    mutate=args.mut,
                    max_mutation_terms_per_relation=(
                        None
                        if args.trace_mutation_limit == 0
                        else args.trace_mutation_limit
                    ),
                    max_mutation_substitutions_per_relation=(
                        None
                        if args.trace_mutation_substitution_limit == 0
                        else args.trace_mutation_substitution_limit
                    ),
                )
                mutation_result = houdini_result.mutation_result
            else:
                # SeedMiner allocates the canonical VariableMap in __init__,
                # independent of the candidate-mining pass performed by
                # .mine(). Only run .mine() when --seed-houdini was
                # requested, so a plain --cands run does not pay for
                # syntactic candidate mining it will not use.
                miner = SeedMiner(program)
                seed_result = miner.mine() if args.seed_houdini else None
                candidates: CandidateMap = (
                    {} if seed_result is None else seed_result.candidates
                )

                if args.cands is not None:
                    user_candidates = parse_candidate_file(args.cands, miner.variables)
                    candidates = merge_candidate_maps(candidates, user_candidates)

                if args.mut:
                    # Applies to whatever's in `candidates` at this point --
                    # seed-mined, user-supplied, or both merged together --
                    # since mutate_candidates only looks at the expressions
                    # themselves.
                    mutation_result = mutate_candidates(candidates)
                    candidates = merge_candidate_maps(
                        candidates, mutation_result.candidates
                    )

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
                        mutation_result=mutation_result,
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
                    mutation_result=mutation_result,
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
