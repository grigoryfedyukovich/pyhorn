"""``examples/mixed_theories/`` previously had only two examples
(``real_string_safe.smt2``, ``int_real_string_safe.smt2``), and both are
easy: SeedMiner mines the exact linear equality/coercion needed and
MultiHoudini finds it on the first pass. This file covers
``coffee_can_step_counter_safe.smt2``, which is not: a genuinely safe
Int+String problem that this tool cannot prove, because the needed
invariant is a modular/parity fact over the String component that no
syntactic candidate mined from the rule or query text can express.

This mirrors, almost exactly, the confirmed-hard test for the pure-String
parent example in ``tests/test_string_invariant_literature.py``
(``test_syntactic_seedminer_does_not_overclaim_hard_regular_problems``,
parametrized over ``coffee_can_odd_white_safe.smt2``). The Int step
counter threaded through this file's signature is easy on its own and
irrelevant to the property being checked -- the bad-state check still
only inspects the String component -- so the difficulty is inherited
from the parent example rather than newly (and, without a working Z3
environment to check it against, unverifiably) hand-derived.
"""

from __future__ import annotations

from pathlib import Path

import z3

from pyhorn_bnd import HoudiniStatus, SeedMiner, parse_chc_file, run_seed_houdini

ROOT = Path(__file__).resolve().parents[1]
MIXED = ROOT / "examples" / "mixed_theories"


def test_coffee_can_step_counter_parses_as_int_and_string() -> None:
    program = parse_chc_file(
        MIXED / "coffee_can_step_counter_safe.smt2", slice_program=False
    )
    assert program.string_sorts.uses_string
    (relation,) = (r for r in program.relations if str(r.name()) == "inv")
    domain = tuple(relation.domain(i) for i in range(relation.arity()))
    assert domain == (z3.IntSort(), z3.StringSort())


def test_coffee_can_step_counter_is_safe_but_unproved_by_seed_houdini() -> None:
    """The property genuinely holds (the parity of the W-count is
    invariant, so the single-bean state "B" is unreachable from "WWWB"),
    but SeedMiner's syntactic mining cannot express a parity/modular
    invariant, so MultiHoudini cannot certify it -- the same outcome
    already confirmed for the pure-String parent example."""
    program = parse_chc_file(
        MIXED / "coffee_can_step_counter_safe.smt2", slice_program=False
    )
    seeds = SeedMiner(program).mine()
    result = run_seed_houdini(program, timeout_ms=2_000, random_seed=1)

    assert seeds.candidate_count > 0
    assert result.status is HoudiniStatus.UNKNOWN
    assert result.failures
