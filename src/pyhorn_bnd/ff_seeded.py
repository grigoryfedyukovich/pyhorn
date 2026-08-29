"""Run forward-fixpoint seeded from individual pieces of a relation's
initial condition, instead of always starting from the whole thing at
once.

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

This tries each fact-rule conjunct (mined via the same
`SeedMiner`/`_boolean_seed_nodes` machinery Seed-Houdini already uses --
see `seedminer.py`) on its own, in turn, and stops at the first one whose
own closure proves the query unreachable. If none do, it falls back to
the full, literal init -- today's default behavior -- so this is never
less capable than running `--ff` directly, only sometimes faster or more
robust getting to the same answer.
"""

from __future__ import annotations

from dataclasses import dataclass

import z3

from .forward_fixpoint import (
    DEFAULT_MAX_ITERATIONS,
    DEFAULT_OVERALL_TIMEOUT_S,
    DEFAULT_TIMEOUT_MS,
    DEFAULT_WIDENING_DELAY,
    ForwardFixpointResult,
    ForwardFixpointStatus,
    run_forward_fixpoint,
)
from .horn import HornProgram
from .seedminer import SeedMiner, VariableMap


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


def run_forward_fixpoint_from_init_conjuncts(
    program: HornProgram,
    *,
    relation: z3.FuncDeclRef | None = None,
    max_iterations: int = DEFAULT_MAX_ITERATIONS,
    timeout_ms: int = DEFAULT_TIMEOUT_MS,
    overall_timeout_s: float = DEFAULT_OVERALL_TIMEOUT_S,
    enable_generalization: bool = True,
    widening_delay: int = DEFAULT_WIDENING_DELAY,
) -> SeededForwardFixpointResult:
    """Try each fact-rule conjunct of *relation* (or, if not given, every
    relation with a fact rule, one relation at a time) as that
    relation's own `initial_seed`, in turn -- every other relation still
    gets its normal, full fact-rule seeding for each attempt. Stops at
    the first SAFE. A confirmed UNSAFE (forward-fixpoint's own
    counterexamples are already independently confirmed -- see
    forward_fixpoint.py's CAUTION note -- this never derives a new one)
    also stops immediately, since it's a genuine proof of the real
    program's unsafety regardless of which seed led to finding it.
    Otherwise, falls back to the full, literal init -- today's default
    `--ff` behavior -- as the last attempt.
    """
    variables = SeedMiner(program).variables
    conjuncts_by_relation = fact_rule_conjuncts(program, variables)
    if relation is not None:
        conjuncts_by_relation = {
            rel: conjuncts
            for rel, conjuncts in conjuncts_by_relation.items()
            if rel is relation
        }

    attempts = 0
    for rel, conjuncts in conjuncts_by_relation.items():
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
                    result=result, seed_used=conjunct, attempts=attempts
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
        result=fallback, seed_used=None, attempts=attempts
    )
