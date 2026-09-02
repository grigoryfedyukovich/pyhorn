"""Alternate Houdini and forward-fixpoint in rounds, each feeding the
other.

Each round:

1. **Houdini, on all candidates at once.** Run :class:`MultiHoudini` on
   the full candidate pool -- SeedMiner's own full syntactic mining
   (fact-, step-, and query-rule provenance alike, always -- see
   `run_ff_houdini`'s own docstring for why this differs from
   `--ff-seeded`'s narrower default), plus whichever of `--cands`,
   `--phasefit`, `--mut`, and `--trace-houdini` were also requested (the
   same sources `ff_seeded.gather_candidate_pool` draws from).
   Every candidate that survives incremental elimination and passes a
   *fresh, independent* re-certification against every non-query rule is
   a genuine, proven invariant of its relation -- that's what
   `MultiHoudini`'s own final certification pass exists to guarantee
   (see `houdini.py`'s `MultiHoudini.run` docstring). If certification
   also clears every *query* rule, Houdini alone has already proven the
   program SAFE -- done, no need for forward-fixpoint at all.

2. **Feed the proven invariants into an accelerated forward-fixpoint
   pass.** Only the query rules are allowed to still fail certification
   here -- a query failure just means the current invariants aren't
   *sufficient* to rule the query out yet, not that anything is unsound.
   (A genuine *non-query* certification failure, on the other hand,
   means nothing survived this round can be trusted as a real invariant,
   so nothing is fed forward that round.) Whatever did certify becomes
   `external_invariants` for one `run_forward_fixpoint` pass: for a rule
   propagating some `P` through its transition relation `TR`, the
   invariants are conjoined in before quantifier elimination, so the
   image computed is the *strongest* `Q` such that `P /\\ TR /\\ Invs =>
   Q` -- tighter, and sometimes able to prove things, than the same
   image without them (see `forward_fixpoint.py`'s `external_invariants`
   field and `docs/forward_fixpoint.md`). The new reachable set for the
   next iteration is `P \\/ Q`, exactly as for an unaccelerated run. A
   SAFE or UNSAFE verdict from this pass stops everything immediately --
   forward-fixpoint's own UNSAFE verdicts are already independently
   re-confirmed against the program's real fact rules regardless of what
   fed the computation (see forward_fixpoint.py's CAUTION note), so this
   never has to re-derive that confirmation itself.

3. **Otherwise, alternate again.** The accelerated pass's own per-relation
   reachable-set formulas -- genuine, freshly-computed facts about the
   program, not syntactic guesses -- are added as new candidates for the
   *next* round's Houdini pass, together with the *entire original*
   candidate pool again, including whatever this round's Houdini pass
   eliminated: a candidate that didn't survive on its own might still
   combine usefully with a newly-computed reachable-set formula. Repeats
   up to a round budget, and stops early -- report UNKNOWN -- the moment
   a round's candidate pool is identical to the previous round's, since
   both Houdini and forward-fixpoint are deterministic and a repeated
   pool can only repeat the same outcome.
"""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum
from pathlib import Path

import z3

from .cands import merge_candidate_maps
from .ff_seeded import gather_candidate_pool
from .forward_fixpoint import (
    DEFAULT_MAX_ITERATIONS,
    DEFAULT_OVERALL_TIMEOUT_S,
    DEFAULT_TIMEOUT_MS,
    DEFAULT_WIDENING_DELAY,
    ForwardFixpointStatus,
    run_forward_fixpoint,
)
from .horn import HornProgram, HornRule
from .houdini import HoudiniStatus, MultiHoudini
from .seedminer import CandidateMap, SeedMiner, VariableMap
from .trace_miner import (
    DEFAULT_MODELS_PER_PREFIX,
    DEFAULT_SAMPLES_PER_RELATION,
    DEFAULT_TRACE_CANDIDATES_PER_RELATION,
    DEFAULT_TRACE_DEPTH,
    DEFAULT_TRACE_LIMIT,
)

DEFAULT_MAX_ROUNDS = 3
# A `reached` formula fed back as a Houdini candidate for the next round
# has to actually be usable as one: MultiHoudini re-certifies every
# candidate against every rule with a fresh solver call each round, and
# an un-widened forward-fixpoint pass's own reachable-set formula can
# grow far beyond anything reasonable for that (a genuine case measured
# during development: ~750,000 characters after 10 non-converging
# iterations on one relation). A formula past this size is dropped
# rather than fed forward -- it was never going to be a productive
# Houdini candidate regardless of what it might have proven.
DEFAULT_MAX_FED_BACK_FORMULA_CHARS = 4_000


class FFHoudiniStatus(Enum):
    SAFE = "safe"
    UNSAFE = "unsafe"
    UNKNOWN = "unknown"


@dataclass(frozen=True)
class FFHoudiniResult:
    status: FFHoudiniStatus
    message: str
    variables: VariableMap
    # How many rounds actually ran before this result (1 if the very
    # first Houdini pass already proved SAFE outright).
    rounds: int
    # Populated on SAFE: relation -> its proven invariant formula --
    # either Houdini's own certified conjunction, or forward-fixpoint's
    # own reachable-set formula for the round that settled it.
    invariants: dict[z3.FuncDeclRef, z3.BoolRef] | None = None
    # Populated on UNSAFE: forward-fixpoint's own genuine, already
    # independently-confirmed counterexample.
    violated_rule: HornRule | None = None
    counterexample_model: str | None = None


def _pool_signature(pool: CandidateMap) -> frozenset[tuple[str, str]]:
    return frozenset(
        (relation.name(), candidate.sexpr())
        for relation, candidates in pool.items()
        for candidate in candidates
    )


def _rule_is_query(program: HornProgram, rule_id: int) -> bool:
    for rule in program.rules:
        if rule.rule_id == rule_id:
            return rule.is_query
    return False


def _as_invariants(candidates: CandidateMap) -> dict[z3.FuncDeclRef, z3.BoolRef]:
    return {
        relation: z3.And(*conjuncts) for relation, conjuncts in candidates.items()
        if conjuncts
    }


def run_ff_houdini(
    program: HornProgram,
    *,
    cands_path: Path | None = None,
    use_phasefit: bool = False,
    use_mut: bool = False,
    use_trace: bool = False,
    trace_depth: int = DEFAULT_TRACE_DEPTH,
    trace_limit: int = DEFAULT_TRACE_LIMIT,
    trace_models_per_prefix: int = DEFAULT_MODELS_PER_PREFIX,
    trace_samples_per_relation: int = DEFAULT_SAMPLES_PER_RELATION,
    trace_candidates_per_relation: int = DEFAULT_TRACE_CANDIDATES_PER_RELATION,
    max_rounds: int = DEFAULT_MAX_ROUNDS,
    max_fed_back_formula_chars: int = DEFAULT_MAX_FED_BACK_FORMULA_CHARS,
    ff_max_iterations: int = DEFAULT_MAX_ITERATIONS,
    ff_timeout_ms: int = DEFAULT_TIMEOUT_MS,
    ff_overall_timeout_s: float = DEFAULT_OVERALL_TIMEOUT_S,
    ff_enable_generalization: bool = True,
    ff_widening_delay: int = DEFAULT_WIDENING_DELAY,
    houdini_timeout_ms: int = 1_000,
    random_seed: int | None = None,
) -> FFHoudiniResult:
    """Run the alternation described in the module docstring, up to
    *max_rounds* times.
    """
    variables = SeedMiner(program).variables
    base_pool, _gathered, _sound = gather_candidate_pool(
        program,
        variables=variables,
        # "ALL candidates" (see the module docstring's step 1) always
        # means the *full* syntactic mining Seed-Houdini itself uses --
        # fact-, step-, and query-rule provenance alike -- not
        # `--ff-seeded`'s own narrower fact-rule-only default. Those two
        # defaults differ for a real reason: `--ff-seeded` needs each
        # candidate to be a sound `initial_seed` *by construction*, with
        # no independent check beyond that; a real Houdini pass verifies
        # inductiveness of *any* candidate itself, regardless of
        # provenance, via its own certification (see this module's
        # docstring) -- so there is no reason to withhold query-rule-
        # derived candidates (often exactly the ones actually needed;
        # `y == 2*x` mined straight from a negated query is the routine
        # case) the way `--ff-seeded` must. `--seed-houdini` therefore has
        # no CLI-visible effect here: forcing this unconditionally is
        # simply what "ALL candidates" already means.
        use_seed_houdini=True,
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

    extra_from_fixpoint: CandidateMap = {}
    previous_signature: frozenset[tuple[str, str]] | None = None

    for round_number in range(1, max_rounds + 1):
        pool = merge_candidate_maps(base_pool, extra_from_fixpoint)
        signature = _pool_signature(pool)
        if signature == previous_signature:
            return FFHoudiniResult(
                status=FFHoudiniStatus.UNKNOWN,
                message=(
                    f"stopped after {round_number - 1} round(s): the "
                    "candidate pool stopped changing, so another round "
                    "would only repeat the same outcome"
                ),
                variables=variables,
                rounds=round_number - 1,
            )
        previous_signature = signature

        houdini_result = MultiHoudini(
            program, variables, timeout_ms=houdini_timeout_ms, random_seed=random_seed
        ).run(pool)

        if houdini_result.status is HoudiniStatus.SUCCESS:
            return FFHoudiniResult(
                status=FFHoudiniStatus.SAFE,
                message=(
                    f"round {round_number}: Houdini certified "
                    f"{sum(len(v) for v in houdini_result.candidates.values())} "
                    "candidate(s) as inductive, ruling out every query directly"
                ),
                variables=variables,
                rounds=round_number,
                invariants=_as_invariants(houdini_result.candidates),
            )

        # UNKNOWN: only trust the surviving candidates as
        # external_invariants if every certification failure is a query
        # rule -- a query failure just means the invariants aren't
        # *sufficient* yet, not that any of them is unsound; a genuine
        # non-query failure means nothing this round can be trusted, so
        # nothing is fed forward (this round falls back to an
        # unaccelerated attempt instead).
        trustworthy = houdini_result.candidates and not any(
            not _rule_is_query(program, failure.rule_id)
            for failure in houdini_result.failures
        )
        external_invariants = (
            _as_invariants(houdini_result.candidates) if trustworthy else None
        )

        ff_result = run_forward_fixpoint(
            program,
            variables=variables,
            max_iterations=ff_max_iterations,
            timeout_ms=ff_timeout_ms,
            overall_timeout_s=ff_overall_timeout_s,
            enable_generalization=ff_enable_generalization,
            widening_delay=ff_widening_delay,
            external_invariants=external_invariants,
        )

        if ff_result.status is ForwardFixpointStatus.SAFE:
            return FFHoudiniResult(
                status=FFHoudiniStatus.SAFE,
                message=f"round {round_number}: {ff_result.message}",
                variables=variables,
                rounds=round_number,
                invariants=dict(ff_result.reached),
            )
        if ff_result.status is ForwardFixpointStatus.UNSAFE:
            return FFHoudiniResult(
                status=FFHoudiniStatus.UNSAFE,
                message=f"round {round_number}: {ff_result.message}",
                variables=variables,
                rounds=round_number,
                violated_rule=ff_result.violated_rule,
                counterexample_model=ff_result.counterexample_model,
            )

        # Neither side settled it -- feed this pass's own per-relation
        # reachable-set formulas back in as new candidates for next
        # round's Houdini pass, on top of the entire original pool again
        # (see the module docstring for why).
        new_candidates: CandidateMap = {
            relation: (formula,)
            for relation, formula in ff_result.reached.items()
            if not z3.is_false(formula)
            and not z3.is_true(formula)
            and len(formula.sexpr()) <= max_fed_back_formula_chars
        }
        extra_from_fixpoint = merge_candidate_maps(extra_from_fixpoint, new_candidates)

    return FFHoudiniResult(
        status=FFHoudiniStatus.UNKNOWN,
        message=f"round budget ({max_rounds}) exhausted without a verdict",
        variables=variables,
        rounds=max_rounds,
    )
