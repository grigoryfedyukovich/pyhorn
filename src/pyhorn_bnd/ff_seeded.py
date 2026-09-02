"""Run forward-fixpoint seeded from individual pieces of a candidate
pool, instead of always starting from the whole thing at once.

By default, forward-fixpoint seeds a relation's round-0 reachable set
from the literal, complete fact-rule condition (see
`ForwardFixpoint.initial_seed`'s docstring for why any *sound* seed --
one Init implies -- works: a seed's own closure avoiding the query is
still a valid proof the true, narrower init's closure does too). Facts
extracted piece by piece are exactly this kind of sound seed, since each
one is individually implied by the full init condition they came from.

Why this can help even though it doesn't change what's *provable*: a
smaller, single-fact seed makes for a smaller, simpler forward-image
computation every round -- fewer variables genuinely in play, simpler
formulas for `qe` to handle. That's not just faster; it's also less
exposed to the class of `qe`-tactic soundness issue documented in
`forward_fixpoint.py`'s own CAUTION note, which in practice showed up on
a large, several-variables-at-once formula, not a small single-fact one.

By default (no --cands/--phasefit/--trace-houdini/--mut/--seed-houdini),
this tries each fact-rule conjunct (mined via the same `SeedMiner`/
`_boolean_seed_nodes` machinery Seed-Houdini already uses -- see
`seedminer.py`) on its own, in turn. Passing --seed-houdini and/or any
of those other flags widens the pool this same way to any of this
codebase's other candidate-generating techniques -- SeedMiner's own full
mining (fact-, step-, and query-rule provenance alike -- unlike
fact-rule conjuncts, this needs --seed-houdini to be explicitly
requested; it is never included just because some other source was),
`--cands`-supplied candidates, `--phasefit`'s interval lemmas,
`--trace-houdini`'s trace-sampled generalizations, and `--mut`'s
pairwise mutations of the combined pool. Unlike fact-rule conjuncts,
none of those are sound as an `initial_seed` by construction, so each
one is checked against **initiation** -- `Init(relation) => candidate`,
via `forward_fixpoint.candidate_passes_initiation` -- and dropped if it
fails, before ever being tried.

Either way, this stops at the first single conjunct/candidate whose own
closure proves the query unreachable. If none do, it falls back to the
full, literal init -- today's default behavior -- so this is never less
capable than running `--ff` directly, only sometimes faster, more
robust, or (once the pool is widened) able to reach a proof plain `--ff`
alone cannot.
"""

from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path

import z3

from .cands import merge_candidate_maps, parse_candidate_file
from .forward_fixpoint import (
    DEFAULT_MAX_ITERATIONS,
    DEFAULT_OVERALL_TIMEOUT_S,
    DEFAULT_TIMEOUT_MS,
    DEFAULT_WIDENING_DELAY,
    ForwardFixpointResult,
    ForwardFixpointStatus,
    candidate_passes_initiation,
    relation_fact_seed,
    run_forward_fixpoint,
)
from .horn import HornProgram
from .seedminer import CandidateMap, SeedMiner, VariableMap, mutate_candidates
from .trace_miner import (
    DEFAULT_MODELS_PER_PREFIX,
    DEFAULT_SAMPLES_PER_RELATION,
    DEFAULT_TRACE_CANDIDATES_PER_RELATION,
    DEFAULT_TRACE_DEPTH,
    DEFAULT_TRACE_LIMIT,
)


def fact_rule_conjuncts(
    program: HornProgram, variables: VariableMap | None = None
) -> dict[z3.FuncDeclRef, list[z3.BoolRef]]:
    """The individual pieces of each relation's fact-rule condition,
    mined the same way Seed-Houdini mines candidates (see
    `seedminer._boolean_seed_nodes`), restricted to observations whose
    provenance is a fact rule specifically -- not the step or query
    rules SeedMiner also mines from. Each piece is, by construction,
    implied by the relation's full fact-rule condition, so any one of
    them is a sound `initial_seed` on its own (see that field's
    docstring in forward_fixpoint.py) -- narrower results (an equality
    weakened to `>=`/`<=`, say) are also included, since they're
    typically simpler to work with and no less sound.

    Deduplicated and returned in a stable order (by the observation's
    original rule id, then insertion order) so repeated calls and
    `run_forward_fixpoint_from_init_conjuncts`'s attempt order are
    deterministic.
    """
    variables = SeedMiner(program).variables if variables is None else variables
    fact_rule_ids = {rule.rule_id for rule in program.rules if rule.is_fact}
    seeds = SeedMiner(program).mine()
    by_relation: dict[z3.FuncDeclRef, list[z3.BoolRef]] = {
        rel: [] for rel in variables
    }
    seen: dict[z3.FuncDeclRef, set[str]] = {rel: set() for rel in variables}
    for observation in seeds.observations:
        if observation.rule_id not in fact_rule_ids:
            continue
        if observation.relation not in by_relation:
            continue
        key = observation.candidate.sexpr()
        if key in seen[observation.relation]:
            continue
        seen[observation.relation].add(key)
        by_relation[observation.relation].append(observation.candidate)
    return by_relation


def gather_candidate_pool(
    program: HornProgram,
    *,
    variables: VariableMap,
    use_seed_houdini: bool = False,
    cands_path: Path | None = None,
    use_phasefit: bool = False,
    use_mut: bool = False,
    use_trace: bool = False,
    trace_depth: int = DEFAULT_TRACE_DEPTH,
    trace_limit: int = DEFAULT_TRACE_LIMIT,
    trace_models_per_prefix: int = DEFAULT_MODELS_PER_PREFIX,
    trace_samples_per_relation: int = DEFAULT_SAMPLES_PER_RELATION,
    trace_candidates_per_relation: int = DEFAULT_TRACE_CANDIDATES_PER_RELATION,
    houdini_timeout_ms: int = 1_000,
    random_seed: int | None = None,
) -> tuple[CandidateMap, int, int]:
    """Build the pool of candidates to try individually as `initial_seed`
    overrides -- see the module docstring for the full list of sources.

    With none of *cands_path*/*use_phasefit*/*use_trace*/*use_seed_houdini*
    given, this is exactly :func:`fact_rule_conjuncts` -- sound by
    construction, so no filtering is needed and every gathered candidate
    is "sound" in the return value below.

    Otherwise, the pool is built from SeedMiner's full mining (only if
    *use_seed_houdini* is explicitly given -- unlike the fact-rule-conjunct
    default, this is never included just because some other source was;
    *use_phasefit* is the one exception, since it needs a mined
    ``SeedMiningResult`` of its own for atom harvesting regardless), each
    requested extra source merged in, and *use_mut* (if requested)
    applied last over the complete combined pool. Every candidate
    gathered this way is then checked against **initiation**
    (``Init(relation) => candidate``, via
    :func:`~pyhorn_bnd.forward_fixpoint.candidate_passes_initiation`) and
    dropped if it fails -- unlike fact-rule conjuncts, nothing guarantees
    one of these actually holds at its relation's own entry point.

    Returns ``(pool, candidates_gathered, candidates_sound)``.
    """
    # use_seed_houdini counts as its own request to broaden here, not
    # just a modifier that only matters once something else already has
    # (a bug found during --ff-houdini development: explicitly asking
    # for --seed-houdini's own full mining should never be a no-op just
    # because nothing else was also given).
    other_sources_requested = (
        cands_path is not None or use_phasefit or use_trace or use_seed_houdini
    )
    if not other_sources_requested:
        by_relation = fact_rule_conjuncts(program, variables)
        pool: CandidateMap = {
            rel: tuple(conjuncts) for rel, conjuncts in by_relation.items() if conjuncts
        }
        total = sum(len(v) for v in pool.values())
        return pool, total, total

    miner = SeedMiner(program)
    seed_result = miner.mine() if use_seed_houdini else None
    candidates: CandidateMap = {} if seed_result is None else seed_result.candidates

    if cands_path is not None:
        user_candidates = parse_candidate_file(cands_path, variables)
        candidates = merge_candidate_maps(candidates, user_candidates)

    if use_phasefit:
        from .phasefit import run_phasefit

        # PhaseFit needs a seed_result of its own for atom harvesting
        # regardless of use_seed_houdini -- see the ordinary Houdini CLI
        # pipeline's own identical reasoning for merging it in when
        # freshly mined here.
        if seed_result is None:
            seed_result = miner.mine()
            candidates = merge_candidate_maps(candidates, seed_result.candidates)
        _pf_results, pf_candidates = run_phasefit(program, seed_result=seed_result)
        candidates = merge_candidate_maps(candidates, pf_candidates)

    if use_trace:
        from .trace_miner import TraceCandidateMiner

        traces = TraceCandidateMiner(
            program,
            variables,
            max_depth=trace_depth,
            max_prefixes=trace_limit,
            models_per_prefix=trace_models_per_prefix,
            max_samples_per_relation=trace_samples_per_relation,
            max_candidates_per_relation=trace_candidates_per_relation,
            timeout_ms=houdini_timeout_ms,
            random_seed=random_seed,
        ).mine()
        candidates = merge_candidate_maps(candidates, traces.candidates)

    if use_mut:
        mutation_result = mutate_candidates(candidates)
        candidates = merge_candidate_maps(candidates, mutation_result.candidates)

    filtered: CandidateMap = {}
    total_gathered = 0
    total_sound = 0
    for relation, conjuncts in candidates.items():
        total_gathered += len(conjuncts)
        if not conjuncts:
            continue
        fact_seed = relation_fact_seed(
            program, relation, variables=variables, timeout_ms=DEFAULT_TIMEOUT_MS
        )
        if fact_seed is None:
            continue
        kept = tuple(
            c
            for c in conjuncts
            if candidate_passes_initiation(
                program, relation, c, fact_seed=fact_seed, variables=variables
            )
        )
        if kept:
            filtered[relation] = kept
            total_sound += len(kept)
    return filtered, total_gathered, total_sound


@dataclass(frozen=True)
class SeededForwardFixpointResult:
    result: ForwardFixpointResult
    # The conjunct that produced `result`, or None if no single conjunct
    # worked and this is the full-init fallback.
    seed_used: z3.BoolRef | None
    # How many conjuncts were tried (including a failed one, if any)
    # before this result -- 0 if `seed_used` is None and the first
    # (only) attempt was the full-init fallback.
    attempts: int
    # Pool sizes -- both equal to `attempts` (or less, if a candidate
    # settled it) in the default, fact-rule-conjunct-only mode, since
    # every one of those is sound by construction; can differ once
    # --cands/--phasefit/--mut/--trace-houdini widen the pool, since some
    # of what's gathered there can fail the initiation check.
    candidates_gathered: int = 0
    candidates_sound: int = 0


def run_forward_fixpoint_from_init_conjuncts(
    program: HornProgram,
    *,
    relation: z3.FuncDeclRef | None = None,
    use_seed_houdini: bool = False,
    cands_path: Path | None = None,
    use_phasefit: bool = False,
    use_mut: bool = False,
    use_trace: bool = False,
    trace_depth: int = DEFAULT_TRACE_DEPTH,
    trace_limit: int = DEFAULT_TRACE_LIMIT,
    trace_models_per_prefix: int = DEFAULT_MODELS_PER_PREFIX,
    trace_samples_per_relation: int = DEFAULT_SAMPLES_PER_RELATION,
    trace_candidates_per_relation: int = DEFAULT_TRACE_CANDIDATES_PER_RELATION,
    houdini_timeout_ms: int = 1_000,
    random_seed: int | None = None,
    max_iterations: int = DEFAULT_MAX_ITERATIONS,
    timeout_ms: int = DEFAULT_TIMEOUT_MS,
    overall_timeout_s: float = DEFAULT_OVERALL_TIMEOUT_S,
    enable_generalization: bool = True,
    widening_delay: int = DEFAULT_WIDENING_DELAY,
) -> SeededForwardFixpointResult:
    """Try each candidate in the pool (see :func:`gather_candidate_pool`
    -- by default, *relation*'s fact-rule conjuncts, or every relation
    with a fact rule, one relation at a time, if *relation* isn't given)
    as that relation's own `initial_seed`, in turn -- every other
    relation still gets its normal, full fact-rule seeding for each
    attempt. Stops at the first SAFE. A confirmed UNSAFE (forward-
    fixpoint's own counterexamples are already independently confirmed --
    see forward_fixpoint.py's CAUTION note -- this never derives a new
    one) also stops immediately, since it's a genuine proof of the real
    program's unsafety regardless of which candidate led to finding it.
    Otherwise, falls back to the full, literal init -- today's default
    `--ff` behavior -- as the last attempt.
    """
    variables = SeedMiner(program).variables
    pool, candidates_gathered, candidates_sound = gather_candidate_pool(
        program,
        variables=variables,
        use_seed_houdini=use_seed_houdini,
        cands_path=cands_path,
        use_phasefit=use_phasefit,
        use_mut=use_mut,
        use_trace=use_trace,
        trace_depth=trace_depth,
        trace_limit=trace_limit,
        trace_models_per_prefix=trace_models_per_prefix,
        trace_samples_per_relation=trace_samples_per_relation,
        trace_candidates_per_relation=trace_candidates_per_relation,
        houdini_timeout_ms=houdini_timeout_ms,
        random_seed=random_seed,
    )
    if relation is not None:
        pool = {rel: conjuncts for rel, conjuncts in pool.items() if rel is relation}

    attempts = 0
    for rel, conjuncts in pool.items():
        for conjunct in conjuncts:
            attempts += 1
            result = run_forward_fixpoint(
                program,
                variables=variables,
                max_iterations=max_iterations,
                timeout_ms=timeout_ms,
                overall_timeout_s=overall_timeout_s,
                enable_generalization=enable_generalization,
                widening_delay=widening_delay,
                initial_seed={rel: conjunct},
            )
            if result.status in (
                ForwardFixpointStatus.SAFE,
                ForwardFixpointStatus.UNSAFE,
            ):
                return SeededForwardFixpointResult(
                    result=result,
                    seed_used=conjunct,
                    attempts=attempts,
                    candidates_gathered=candidates_gathered,
                    candidates_sound=candidates_sound,
                )

    fallback = run_forward_fixpoint(
        program,
        variables=variables,
        max_iterations=max_iterations,
        timeout_ms=timeout_ms,
        overall_timeout_s=overall_timeout_s,
        enable_generalization=enable_generalization,
        widening_delay=widening_delay,
    )
    return SeededForwardFixpointResult(
        result=fallback,
        seed_used=None,
        attempts=attempts,
        candidates_gathered=candidates_gathered,
        candidates_sound=candidates_sound,
    )
