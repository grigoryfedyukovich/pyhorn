"""Alternating combination of forward-fixpoint reachability and Houdini
candidate-based induction.

Both :mod:`.forward_fixpoint` and :mod:`.houdini` can independently fail
to prove a program safe for complementary reasons:

* forward-fixpoint's generalized (interval-widened) track can reach a
  genuine fixpoint that is still too loose to rule out a query -- it's a
  sound invariant, just not one that proves anything on its own, because
  interval widening is non-relational and drops correlations between
  variables (see :mod:`.forward_fixpoint`'s own docstring).
* Houdini needs a *complete enough* candidate pool to work with; its
  syntactic mining (:class:`~pyhorn_bnd.seedminer.SeedMiner`) can guess
  relational facts well but has no notion of interval widening, so a
  program whose safety genuinely depends on a pure bound (a widened fact
  with no counterpart anywhere in the program's own text) can defeat it
  even when every other needed fact is easy to guess.

This module alternates between them: forward-fixpoint's generalized
fixpoint, when it finds one, is merged into Houdini's candidate pool as
an extra (always-true, so never at risk of being incorrectly eliminated
-- see below) candidate; and, symmetrically, once Houdini's own
elimination loop stabilizes for a relation, that relation's surviving
candidate conjunction is proven closed under every fact and step rule
(not just query rules) and can be fed back into forward-fixpoint as an
``external_invariants`` fact, tightening (or entirely replacing, for a
tainted relation) what forward-fixpoint would otherwise have to derive
from raw ENTRY facts on its own. Either direction alone already used to
fail on real inputs (see ``test_ff_alone_and_houdini_alone_both_fail``);
the combination handles them.

Why merging a forward-fixpoint invariant into Houdini's candidate pool
never needs any special "pinning" protection: Houdini's elimination
removes a candidate only when a genuine countermodel falsifies it (see
:mod:`.houdini`). A generalized-track fixpoint is, by construction, a
sound over-approximation of the true reachable set -- unconditionally
true for every actual rule application -- so no real countermodel can
ever falsify it. It simply survives filtering untouched, the same way a
correct hand-written candidate would.

Why it's safe to feed Houdini's *intermediate* (not just final-success)
candidates back to forward-fixpoint: ``MultiHoudini``'s own elimination
loop runs to its own internal fixed point -- no further candidate can be
removed -- *before* the separate, independent final certification step
that additionally checks query rules. That internal fixed point already
means every retained candidate is closed under every fact and step rule
(:meth:`MultiHoudini._check_transition` is exactly this check, for every
rule with ``is_query`` False). So when the *only* certification failures
are on query rules, the retained candidate conjunction per relation is a
genuine invariant regardless of whether the overall run counts as a
success -- it just isn't tight enough to rule out the query yet. If any
non-query rule also fails certification (should be rare -- ordinarily a
sign of a solver `unknown` rather than an actual gap, since the
elimination loop's own checks already covered the same rules), this
module conservatively stops alternating rather than risk feeding back
something that was never actually confirmed closed.
"""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum

import z3

from .cands import CandidateMap, merge_candidate_maps
from .forward_fixpoint import (
    DEFAULT_MAX_ITERATIONS,
    DEFAULT_OVERALL_TIMEOUT_S,
    DEFAULT_TIMEOUT_MS,
    DEFAULT_WIDENING_DELAY,
    ForwardFixpointStatus,
    run_forward_fixpoint,
)
from .horn import HornProgram, HornRule
from .houdini import HoudiniStatus, run_seed_houdini, run_trace_houdini
from .seedminer import SeedMiner, VariableMap

DEFAULT_MAX_ROUNDS = 3


class FFHoudiniStatus(Enum):
    SAFE = "safe"
    UNSAFE = "unsafe"
    UNKNOWN = "unknown"


@dataclass(frozen=True)
class FFHoudiniResult:
    status: FFHoudiniStatus
    rounds: int
    message: str
    variables: VariableMap
    # Populated on SAFE: the proof, one relation to its (possibly
    # single-element) conjunction of invariant conjuncts.
    invariants: CandidateMap | None = None
    # Populated on UNSAFE: forward-fixpoint's own genuine counterexample
    # (this module only ever reports UNSAFE by delegating to
    # forward-fixpoint's own already-independently-confirmed verdict --
    # see forward_fixpoint.py's CAUTION note -- never derived here).
    violated_rule: HornRule | None = None
    counterexample_model: str | None = None


def run_ff_houdini(
    program: HornProgram,
    *,
    use_trace: bool = False,
    max_rounds: int = DEFAULT_MAX_ROUNDS,
    ff_max_iterations: int = DEFAULT_MAX_ITERATIONS,
    ff_timeout_ms: int = DEFAULT_TIMEOUT_MS,
    ff_overall_timeout_s: float = DEFAULT_OVERALL_TIMEOUT_S,
    ff_enable_generalization: bool = True,
    ff_widening_delay: int = DEFAULT_WIDENING_DELAY,
    houdini_timeout_ms: int = 1_000,
    random_seed: int | None = None,
    trace_depth: int = 8,
) -> FFHoudiniResult:
    """Alternate forward-fixpoint and Houdini until one proves the
    program safe or unsafe, neither makes further progress, or
    *max_rounds* is exhausted.

    *use_trace* selects Trace-Houdini (mines from bounded sample traces
    as well as syntax) instead of plain Seed-Houdini for the Houdini
    side of each round.

    ``variables`` is built once, from :class:`~pyhorn_bnd.seedminer.SeedMiner`,
    and threaded explicitly through both forward-fixpoint and Houdini for
    the whole run -- they must agree on the exact same canonical
    variables for a relation, or a formula computed by one would be
    merged with, or compared against, the wrong symbols entirely for the
    other. Do not let either component derive its own canonical variables
    independently when combining them this way.
    """
    variables = SeedMiner(program).variables
    rules_by_id = {rule.rule_id: rule for rule in program.rules}

    external_invariants: dict[z3.FuncDeclRef, z3.BoolRef] = {}
    extra_candidates: CandidateMap = {}
    # Keyed by relation -> sexpr, to detect "nothing changed since the
    # last round" without relying on z3.BoolRef equality (which builds an
    # expression rather than comparing one -- see the module tests).
    previous_invariant_shape: dict[z3.FuncDeclRef, str] = {}

    round_num = 0
    for round_num in range(1, max_rounds + 1):
        ff_result = run_forward_fixpoint(
            program,
            variables=variables,
            max_iterations=ff_max_iterations,
            timeout_ms=ff_timeout_ms,
            overall_timeout_s=ff_overall_timeout_s,
            enable_generalization=ff_enable_generalization,
            widening_delay=ff_widening_delay,
            external_invariants=external_invariants or None,
        )

        if ff_result.status is ForwardFixpointStatus.SAFE:
            return FFHoudiniResult(
                status=FFHoudiniStatus.SAFE,
                rounds=round_num,
                message=f"round {round_num}: forward-fixpoint -- {ff_result.message}",
                variables=variables,
                invariants={rel: (f,) for rel, f in ff_result.reached.items()},
            )
        if ff_result.status is ForwardFixpointStatus.UNSAFE:
            return FFHoudiniResult(
                status=FFHoudiniStatus.UNSAFE,
                rounds=round_num,
                message=f"round {round_num}: forward-fixpoint -- {ff_result.message}",
                variables=variables,
                violated_rule=ff_result.violated_rule,
                counterexample_model=ff_result.counterexample_model,
            )

        # UNKNOWN from forward-fixpoint. If its generalized track found
        # its own (sound, if not tight enough) fixpoint, offer it to
        # Houdini -- see the module docstring for why this never needs
        # any special protection against being incorrectly eliminated.
        if ff_result.generalized_invariant:
            extra_candidates = merge_candidate_maps(
                extra_candidates,
                {
                    rel: (formula,)
                    for rel, formula in ff_result.generalized_invariant.items()
                    if rel in variables and not z3.is_true(formula)
                },
            )

        if use_trace:
            houdini_result = run_trace_houdini(
                program,
                trace_depth=trace_depth,
                timeout_ms=houdini_timeout_ms,
                random_seed=random_seed,
                extra_candidates=extra_candidates or None,
            )
        else:
            houdini_result = run_seed_houdini(
                program,
                timeout_ms=houdini_timeout_ms,
                random_seed=random_seed,
                extra_candidates=extra_candidates or None,
            )

        if houdini_result.status is HoudiniStatus.SUCCESS:
            return FFHoudiniResult(
                status=FFHoudiniStatus.SAFE,
                rounds=round_num,
                message=f"round {round_num}: Houdini certified safety",
                variables=houdini_result.variables,
                invariants=houdini_result.candidates,
            )

        # UNKNOWN from Houdini too. Only safe to feed its candidates back
        # to forward-fixpoint as external facts if every certification
        # failure is on a query rule -- see the module docstring.
        non_query_failures = [
            failure
            for failure in houdini_result.failures
            if not rules_by_id[failure.rule_id].is_query
        ]
        if non_query_failures:
            break

        new_external_invariants = {
            rel: z3.And(*conjuncts)
            for rel, conjuncts in houdini_result.candidates.items()
            if conjuncts
        }
        new_shape = {
            rel: formula.sexpr() for rel, formula in new_external_invariants.items()
        }
        if new_shape == previous_invariant_shape:
            # Nothing changed since the last round -- further rounds
            # would just repeat the same work for the same result.
            break
        previous_invariant_shape = new_shape
        external_invariants = new_external_invariants

    return FFHoudiniResult(
        status=FFHoudiniStatus.UNKNOWN,
        rounds=round_num,
        message=(
            f"no proof found within {round_num} round(s) of alternation "
            f"(max_rounds={max_rounds})"
        ),
        variables=variables,
    )
