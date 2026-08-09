"""Tests for the String+Int examples ported from pyhorn-bounded-explorer
0.0.15's ``examples/string_length_literature/`` suite (a divergent branch
that added these literature-derived length benchmarks but never gained
this branch's ``--cands`` / ``--validate-candidates`` feature).

These three add: multi-predicate phase transfer, regex combined with a
length range, and an additional unsafe counterexample shape -- coverage
``tests/test_string_theory.py`` didn't already have. The two "confirmed
real"/"promising" candidate-validation examples ported alongside them
(``bounded_append_safe.smt2``) are covered separately in
``tests/test_candidate_validation_theories.py`` and
``tests/test_cands_theories.py``.
"""

from __future__ import annotations

from pathlib import Path

from pyhorn_bnd import (
    BoundedExplorer,
    ExplorationStatus,
    HoudiniStatus,
    parse_chc_file,
    run_seed_houdini,
)

ROOT = Path(__file__).resolve().parents[1]
EXAMPLES = ROOT / "examples" / "string_theory"


def test_multiphase_length_transfer_parses_two_predicates() -> None:
    program = parse_chc_file(
        EXAMPLES / "multiphase_length_transfer_safe.smt2",
        slice_program=False,
    )
    names = {str(relation.name()) for relation in program.relations}
    assert {"fill", "drain"} <= names


def test_multiphase_length_transfer_is_proved_safe_by_seed_houdini() -> None:
    program = parse_chc_file(
        EXAMPLES / "multiphase_length_transfer_safe.smt2",
        slice_program=False,
    )
    result = run_seed_houdini(program, timeout_ms=5_000, random_seed=1)
    assert result.status is HoudiniStatus.SUCCESS


def test_password_policy_uses_regular_expressions() -> None:
    program = parse_chc_file(
        EXAMPLES / "password_policy_safe.smt2",
        slice_program=False,
    )
    assert program.string_sorts.uses_string
    assert program.string_sorts.uses_regular_expressions


def test_password_policy_is_proved_safe_by_seed_houdini() -> None:
    program = parse_chc_file(
        EXAMPLES / "password_policy_safe.smt2",
        slice_program=False,
    )
    result = run_seed_houdini(program, timeout_ms=5_000, random_seed=1)
    assert result.status is HoudiniStatus.SUCCESS


def test_length_counter_desync_is_found_by_bounded_exploration() -> None:
    """Appending two characters per step while incrementing the ghost
    counter by only one desyncs `str.len s` from `n` on the very first
    step -- the same shape as examples/string_theory/disequality_unsafe.smt2,
    where the query check itself counts as one further step beyond the
    state that actually violates the invariant."""
    program = parse_chc_file(EXAMPLES / "length_counter_desync_unsafe.smt2")
    for solver_mode in ("pool", "fresh"):
        result = BoundedExplorer(
            program, timeout_ms=5_000, solver_mode=solver_mode
        ).explore(upto=6)
        assert result.status is ExplorationStatus.COUNTEREXAMPLE
        assert result.explored_upto == 3
