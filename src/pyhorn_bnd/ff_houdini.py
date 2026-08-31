"""Forward-fixpoint propagation seeded from a flexible pool of candidates.

`--ff-houdini` generalizes `--ff-seeded`'s "try one sound fact-rule
conjunct at a time as `initial_seed`" strategy (see `ff_seeded.py`) from a
single, fixed candidate source (SeedMiner's fact-rule-provenance atoms) to
*any* of this codebase's candidate-generating techniques, in any
combination:

* By default: SeedMiner's own full syntactic mining
  (:meth:`~pyhorn_bnd.seedminer.SeedMiner.mine`) -- fact-, step-, and
  query-rule provenance alike, exactly what ``--seed-houdini`` mines for
  the ordinary Houdini pipeline.
* ``--cands``: user-supplied candidates from an SMT-LIB2 ``define-fun``
  file (:func:`~pyhorn_bnd.cands.parse_candidate_file`).
* ``--phasefit``: PhaseFit's per-branch closed-form interval lemmas
  (:func:`~pyhorn_bnd.phasefit.run_phasefit`).
* ``--trace-houdini``: bounded concrete-sample generalizations
  (:class:`~pyhorn_bnd.trace_miner.TraceCandidateMiner`).
* ``--mut``: pairwise-combined candidates
  (:func:`~pyhorn_bnd.seedminer.mutate_candidates`), applied last, over
  the full pool assembled from whichever of the above were requested.

Every candidate gathered this way -- regardless of source -- is a plain
formula over its relation's canonical variables, with no guarantee it
actually holds at that relation's own entry point: a step- or
query-rule-derived seed atom, a PhaseFit lemma, a trace-sampled
generalization, or a user's own guess can all just as easily describe a
*later* reachable state as an initial one. Before any of them is ever
handed to :func:`~pyhorn_bnd.forward_fixpoint.run_forward_fixpoint` as an
``initial_seed`` override, it must pass an **initiation** check:
``Init(relation) => candidate``, via
:func:`~pyhorn_bnd.forward_fixpoint.candidate_passes_initiation`. This is
exactly the soundness condition ``ForwardFixpoint.run`` itself already
enforces (raising ``ValueError`` if violated) for any ``initial_seed`` --
checking it here upfront lets a whole pool of untrusted candidates be
filtered down to the sound ones instead of finding out one at a time via
that exception. See `forward_fixpoint.py`'s ``initial_seed`` field
docstring for why any formula implied by the real init is always a safe
basis for a proof, in both directions -- SAFE by the same "superset seed"
argument the generalized track and ``external_invariants`` rely on;
UNSAFE because a candidate counterexample is independently re-confirmed
against the program's own real fact rules via
:class:`~pyhorn_bnd.explorer.BoundedExplorer`, entirely independent of
whatever seed produced it. This soundness argument does not depend on the
seed's provenance in any way, which is exactly what makes broadening the
source pool here safe to do at all.

Once the pool is filtered down to initiation-sound candidates, each
survivor is tried on its own, in turn, precisely the way `ff_seeded.py`
tries each fact-rule conjunct: every relation other than the one being
seeded still gets its own normal, full fact-rule seeding, and the attempt
stops at the first SAFE or confirmed UNSAFE. There is no further fallback
to a "whole formula" attempt (seeding every relation from its full,
literal fact-rule condition at once, or filtering the *entire* candidate
pool together through ``MultiHoudini``'s elimination loop, as an earlier
version of this module did by alternating full `--ff` runs with full
Houdini runs): per `docs/forward_fixpoint.md`'s own measurement, a
smaller, single-fact seed is not just cheaper than a joint computation
over every variable at once -- it can outright prove things the joint
computation cannot, since variables a query genuinely doesn't depend on
can make quantifier elimination *less* able to find a proof, not just
slower. Trying every sound candidate individually, one relation at a
time, is this module's only mechanism now; if nothing in the pool settles
the question, the result is UNKNOWN.

By default -- no ``--cands``/``--phasefit``/``--mut``/``--trace-houdini``
-- this pool is exactly SeedMiner's own mining, so ``--ff-houdini`` is
"seed-mining, tried individually" out of the box. Every one of those four
flags is purely additive here: `--ff-houdini` no longer runs its own
fixed internal mining that other candidate sources can't be combined
with, so it is compatible with every one of ``--seed-houdini``,
``--cands``, ``--phasefit``, ``--mut``, ``--trace-houdini``, and
``--ff-seeded``.

``--seed-houdini`` is only ever a genuine toggle once one of ``--cands``,
``--phasefit``, or ``--trace-houdini`` is also given -- exactly like it
is for the ordinary Houdini CLI pipeline: with none of those three
given, SeedMiner's mining runs regardless (that is the default pool
above), so ``--seed-houdini`` has nothing to add there; ``--ff-seeded``
likewise has no separate effect alongside ``--ff-houdini``, since trying
individual sound seeds one at a time is exactly what this module already
does by default (see the CLI help text). But once ``--cands`` and/or
``--trace-houdini`` narrow the pool to just what was actually asked for
(see :func:`gather_candidate_pool`), adding ``--seed-houdini`` back in
genuinely broadens it again. ``--phasefit`` is the one exception: it
needs a mined ``SeedMiningResult`` of its own for atom harvesting
regardless, so its candidates end up in the pool either way, matching
the ordinary Houdini CLI pipeline's own documented reasoning for the
same situation.
"""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum
from pathlib import Path

import z3

from .cands import merge_candidate_maps, parse_candidate_file
from .forward_fixpoint import (
    DEFAULT_MAX_ITERATIONS,
    DEFAULT_OVERALL_TIMEOUT_S,
    DEFAULT_TIMEOUT_MS,
    DEFAULT_WIDENING_DELAY,
    ForwardFixpointStatus,
    candidate_passes_initiation,
    relation_fact_seed,
    run_forward_fixpoint,
)
from .horn import HornProgram, HornRule
from .seedminer import CandidateMap, SeedMiner, VariableMap, mutate_candidates
from .trace_miner import (
    DEFAULT_MODELS_PER_PREFIX,
    DEFAULT_SAMPLES_PER_RELATION,
    DEFAULT_TRACE_CANDIDATES_PER_RELATION,
    DEFAULT_TRACE_DEPTH,
    DEFAULT_TRACE_LIMIT,
)


class FFHoudiniStatus(Enum):
    SAFE = "safe"
    UNSAFE = "unsafe"
    UNKNOWN = "unknown"


@dataclass(frozen=True)
class FFHoudiniResult:
    status: FFHoudiniStatus
    message: str
    variables: VariableMap
    # Size of the gathered candidate pool before the initiation filter
    # (summed across every relation).
    candidates_gathered: int
    # How many of those passed the initiation check (Init => candidate)
    # and were therefore actually available to try.
    candidates_sound: int
    # How many were actually handed to forward-fixpoint before this
    # result -- a confirmed SAFE/UNSAFE stops immediately, so this can be
    # less than candidates_sound.
    attempts: int
    # The relation and candidate whose individual propagation produced
    # this result, or None if nothing in the pool did (status is then
    # UNKNOWN -- see the module docstring for why there is no further
    # fallback to try after that).
    winning_relation: z3.FuncDeclRef | None = None
    winning_candidate: z3.BoolRef | None = None
    # Populated on SAFE: relation -> its reachable-set formula, exactly
    # as forward-fixpoint's own `reached` reports it for the winning run.
    invariants: dict[z3.FuncDeclRef, z3.BoolRef] | None = None
    # Populated on UNSAFE: forward-fixpoint's own genuine counterexample
    # (this module only ever reports UNSAFE by delegating to
    # forward-fixpoint's own already-independently-confirmed verdict --
    # see forward_fixpoint.py's CAUTION note -- never derived here).
    violated_rule: HornRule | None = None
    counterexample_model: str | None = None


def gather_candidate_pool(
    program: HornProgram,
    *,
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
) -> tuple[CandidateMap, VariableMap]:
    """Build the pool of candidates ``--ff-houdini`` will try individually
    as forward-fixpoint seeds -- see the module docstring for the full
    list of sources and why mixing them is safe.

    SeedMiner's full mining is the pool's base by default -- when none of
    *cands_path*/*use_phasefit*/*use_trace* is given, mining always runs
    regardless of *use_seed_houdini*, exactly the "by default it's only
    from seeds" behavior. Once any of those three is given instead,
    mining becomes gated by *use_seed_houdini*, exactly like the ordinary
    Houdini CLI pipeline's own ``--seed-houdini`` flag: the pool is built
    "wrt the options" the caller actually asked for, not silently
    including the default source too. ``use_mut`` never gates this --
    it only ever applies afterwards, over whatever pool resulted -- and
    ``use_phasefit`` is the one documented exception to the gate itself
    (see below), matching that same CLI pipeline's own precedent there.

    Whichever extra sources are requested are then merged in, and
    finally ``--mut`` (if requested) is applied last, over the complete
    combined pool -- the same ordering the ordinary Houdini CLI pipeline
    uses for the same flags.
    """
    miner = SeedMiner(program)
    other_sources_requested = (
        cands_path is not None or use_phasefit or use_trace
    )
    seed_result = (
        miner.mine() if (use_seed_houdini or not other_sources_requested) else None
    )
    candidates: CandidateMap = {} if seed_result is None else seed_result.candidates

    if cands_path is not None:
        user_candidates = parse_candidate_file(cands_path, miner.variables)
        candidates = merge_candidate_maps(candidates, user_candidates)

    if use_phasefit:
        from .phasefit import run_phasefit

        # PhaseFit needs a seed_result of its own for atom harvesting
        # regardless of use_seed_houdini. If we have to mine it fresh
        # here, merge its candidates into the pool too -- otherwise
        # relations PhaseFit doesn't touch (or fails to split) would get
        # no candidates at all from a --phasefit-only run, exactly the
        # reasoning the ordinary Houdini CLI pipeline documents for the
        # same situation. This is the one source use_seed_houdini cannot
        # actually gate off.
        if seed_result is None:
            seed_result = miner.mine()
            candidates = merge_candidate_maps(candidates, seed_result.candidates)
        _pf_results, pf_candidates = run_phasefit(program, seed_result=seed_result)
        candidates = merge_candidate_maps(candidates, pf_candidates)

    if use_trace:
        from .trace_miner import TraceCandidateMiner

        traces = TraceCandidateMiner(
            program,
            miner.variables,
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

    return candidates, miner.variables


def _filter_by_initiation(
    program: HornProgram,
    candidates: CandidateMap,
    *,
    variables: VariableMap,
    timeout_ms: int,
    overall_timeout_s: float,
) -> tuple[CandidateMap, int, int]:
    """Keep only the candidates that pass the initiation check
    (``Init(relation) => candidate``) for their own relation -- see
    :func:`~pyhorn_bnd.forward_fixpoint.candidate_passes_initiation`.
    *relation*'s own fact condition is computed once and reused for every
    one of its candidates rather than recomputed per candidate.

    Returns ``(filtered_pool, total_gathered, total_sound)``.
    """
    filtered: CandidateMap = {}
    total_gathered = 0
    total_sound = 0
    for relation, conjuncts in candidates.items():
        total_gathered += len(conjuncts)
        if not conjuncts:
            continue
        fact_seed = relation_fact_seed(
            program,
            relation,
            variables=variables,
            timeout_ms=timeout_ms,
            overall_timeout_s=overall_timeout_s,
        )
        if fact_seed is None:
            # QE couldn't even compute Init for this relation -- nothing
            # here can be confirmed sound, so nothing of its is tried.
            continue
        kept = tuple(
            candidate
            for candidate in conjuncts
            if candidate_passes_initiation(
                program,
                relation,
                candidate,
                fact_seed=fact_seed,
                variables=variables,
                timeout_ms=timeout_ms,
                overall_timeout_s=overall_timeout_s,
            )
        )
        if kept:
            filtered[relation] = kept
            total_sound += len(kept)
    return filtered, total_gathered, total_sound


def run_ff_houdini(
    program: HornProgram,
    *,
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
    ff_max_iterations: int = DEFAULT_MAX_ITERATIONS,
    ff_timeout_ms: int = DEFAULT_TIMEOUT_MS,
    ff_overall_timeout_s: float = DEFAULT_OVERALL_TIMEOUT_S,
    ff_enable_generalization: bool = True,
    ff_widening_delay: int = DEFAULT_WIDENING_DELAY,
    houdini_timeout_ms: int = 1_000,
    random_seed: int | None = None,
) -> FFHoudiniResult:
    """Gather a candidate pool (see :func:`gather_candidate_pool`), keep
    only the initiation-sound candidates (see :func:`_filter_by_initiation`),
    and try each one individually as forward-fixpoint's ``initial_seed`` --
    stopping at the first SAFE or confirmed UNSAFE. UNKNOWN if nothing in
    the pool settles it; see the module docstring for why there is no
    further "whole formula" fallback to try after that.
    """
    candidates, variables = gather_candidate_pool(
        program,
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
    sound_pool, candidates_gathered, candidates_sound = _filter_by_initiation(
        program,
        candidates,
        variables=variables,
        timeout_ms=ff_timeout_ms,
        overall_timeout_s=ff_overall_timeout_s,
    )

    attempts = 0
    for relation, conjuncts in sound_pool.items():
        for candidate in conjuncts:
            attempts += 1
            result = run_forward_fixpoint(
                program,
                variables=variables,
                max_iterations=ff_max_iterations,
                timeout_ms=ff_timeout_ms,
                overall_timeout_s=ff_overall_timeout_s,
                enable_generalization=ff_enable_generalization,
                widening_delay=ff_widening_delay,
                initial_seed={relation: candidate},
            )
            if result.status is ForwardFixpointStatus.SAFE:
                return FFHoudiniResult(
                    status=FFHoudiniStatus.SAFE,
                    message=(
                        f"seeded {relation.name()} from candidate "
                        f"{candidate} -- {result.message}"
                    ),
                    variables=variables,
                    candidates_gathered=candidates_gathered,
                    candidates_sound=candidates_sound,
                    attempts=attempts,
                    winning_relation=relation,
                    winning_candidate=candidate,
                    invariants=dict(result.reached),
                )
            if result.status is ForwardFixpointStatus.UNSAFE:
                return FFHoudiniResult(
                    status=FFHoudiniStatus.UNSAFE,
                    message=(
                        f"seeded {relation.name()} from candidate "
                        f"{candidate} -- {result.message}"
                    ),
                    variables=variables,
                    candidates_gathered=candidates_gathered,
                    candidates_sound=candidates_sound,
                    attempts=attempts,
                    winning_relation=relation,
                    winning_candidate=candidate,
                    violated_rule=result.violated_rule,
                    counterexample_model=result.counterexample_model,
                )

    return FFHoudiniResult(
        status=FFHoudiniStatus.UNKNOWN,
        message=(
            f"none of {candidates_sound} initiation-sound candidate(s) "
            f"(out of {candidates_gathered} gathered) settled the "
            "question -- no whole-formula fallback is attempted (see "
            "module docstring)"
        ),
        variables=variables,
        candidates_gathered=candidates_gathered,
        candidates_sound=candidates_sound,
        attempts=attempts,
    )
