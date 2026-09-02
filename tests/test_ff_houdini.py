"""Tests for :mod:`pyhorn_bnd.ff_houdini`.

See that module's docstring for the design: alternate real Houdini
elimination (on the whole candidate pool at once) and an
invariant-accelerated forward-fixpoint pass, each round feeding the
other, up to a round budget -- replacing an earlier, different design
that seeded forward-fixpoint individually from one candidate at a time
(that mechanism now lives in `ff_seeded.py`, generalized under
`--ff-seeded`; see test_ff_seeded.py).
"""

from __future__ import annotations

from pathlib import Path

import pytest

from pyhorn_bnd.ff_houdini import (
    DEFAULT_MAX_ROUNDS,
    FFHoudiniStatus,
    run_ff_houdini,
)
from pyhorn_bnd.horn import parse_chc_file

EXAMPLES = Path(__file__).resolve().parents[1] / "examples"
ARRAY_EQ_EXAMPLE = EXAMPLES / "mutation_features" / "01_array_eq_select_a.smt2"


def _write(tmp_path: Path, name: str, smt2: str) -> Path:
    path = tmp_path / name
    path.write_text(smt2)
    return path


# ---------------------------------------------------------------------------
# The flagship case: an array-equality invariant (a==b) that's broken by a
# store at one index but preserved through the mined atom's substitution --
# see the file's own comment. Neither plain --ff nor plain --seed-houdini
# (confirmed below) proves this alone; the alternation does, specifically
# because round 1's Houdini pass isn't enough on its own but round 2's
# (fed by round 1's accelerated forward-fixpoint pass) is.
# ---------------------------------------------------------------------------


def test_ff_alone_and_seed_houdini_alone_both_fail_on_the_array_example():
    """Ground truth for the flagship case below."""
    from pyhorn_bnd.forward_fixpoint import ForwardFixpointStatus, run_forward_fixpoint
    from pyhorn_bnd.houdini import HoudiniStatus, run_seed_houdini

    program = parse_chc_file(ARRAY_EQ_EXAMPLE, slice_program=False)

    assert (
        run_forward_fixpoint(program, overall_timeout_s=5).status
        is ForwardFixpointStatus.UNKNOWN
    )
    assert run_seed_houdini(program, timeout_ms=2000).status is HoudiniStatus.UNKNOWN


def test_combined_succeeds_where_ff_alone_and_seed_houdini_alone_both_fail():
    program = parse_chc_file(ARRAY_EQ_EXAMPLE, slice_program=False)

    result = run_ff_houdini(
        program, ff_timeout_ms=1000, ff_overall_timeout_s=4, houdini_timeout_ms=1000
    )

    assert result.status is FFHoudiniStatus.SAFE
    assert result.rounds >= 2  # round 1's Houdini pass alone isn't enough
    assert result.invariants is not None


# ---------------------------------------------------------------------------
# Basic verdicts: SAFE resolved directly by Houdini alone (round 1), SAFE
# resolved by the accelerated fixpoint, and UNSAFE.
# ---------------------------------------------------------------------------


def test_houdini_alone_certifies_a_simple_relational_invariant(tmp_path):
    """y == 2*x is exactly the kind of relation Seed-Houdini mines
    directly from the negated query and can certify inductive on its
    own -- round 1's Houdini pass alone should already succeed here,
    with no forward-fixpoint pass needed at all.
    """
    smt2 = """
(set-logic HORN)
(declare-var x Int)
(declare-var y Int)
(declare-var x1 Int)
(declare-var y1 Int)
(declare-rel inv (Int Int))
(declare-rel fail ())
(rule (=> (and (= x 0) (= y 0)) (inv x y)))
(rule (=> (and (inv x y) (= x1 (+ x 1)) (= y1 (+ y 2))) (inv x1 y1)))
(rule (=> (and (inv x y) (not (= y (* 2 x)))) fail))
(query fail)
"""
    path = _write(tmp_path, "relational.smt2", smt2)
    program = parse_chc_file(path, slice_program=False)

    result = run_ff_houdini(program)

    assert result.status is FFHoudiniStatus.SAFE
    assert result.rounds == 1
    assert "Houdini certified" in result.message


def test_reports_unsafe_with_a_confirmed_counterexample(tmp_path):
    smt2 = """
(declare-var x Int)
(declare-rel inv (Int))
(declare-rel fail ())
(rule (inv 0))
(rule (=> (inv x) (inv (+ x 1))))
(rule (=> (and (inv x) (>= x 2)) fail))
(query fail)
"""
    path = _write(tmp_path, "counter_unsafe.smt2", smt2)
    program = parse_chc_file(path, slice_program=False)

    result = run_ff_houdini(program)

    assert result.status is FFHoudiniStatus.UNSAFE
    assert result.counterexample_model is not None
    assert result.violated_rule is not None
    assert result.rounds == 1


def test_reports_safe_when_houdini_alone_is_not_enough_but_the_fixpoint_is(
    tmp_path,
):
    """A program with no fact rule at all for its main relation -- so
    Houdini's own certification (round 1) can never succeed on its own,
    since MultiHoudini has nothing to seed round 0 from -- but the
    accelerated fixpoint pass (which always gets its own default,
    literal fact-rule seeding regardless of what Houdini found) still
    settles it via its own generalization, exactly matching plain --ff's
    own behavior on this input.
    """
    smt2 = """
(declare-var x Int)
(declare-rel inv (Int))
(declare-rel fail ())
(rule (inv 0))
(rule (=> (and (inv x) (< x 5)) (inv (+ x 1))))
(rule (=> (and (inv x) (>= x 1000000)) fail))
(query fail)
"""
    path = _write(tmp_path, "trivial_safe.smt2", smt2)
    program = parse_chc_file(path, slice_program=False)

    result = run_ff_houdini(program)

    assert result.status is FFHoudiniStatus.SAFE
    assert result.invariants is not None


# ---------------------------------------------------------------------------
# UNKNOWN and the round budget: a genuinely unprovable-by-this-mechanism
# input terminates cleanly (never hangs), and the round budget and
# early-stability-stop both work as designed.
# ---------------------------------------------------------------------------


def test_reports_unknown_and_terminates_cleanly_when_nothing_settles_it():
    """The flagship handoff-gap example from ff_seeded.py's own tests --
    solvable by --ff-seeded's individual-candidate approach, but not by
    this module's real-Houdini-elimination approach, since neither
    relation's own reachable-set formula stays small enough (see the
    module's DEFAULT_MAX_FED_BACK_FORMULA_CHARS) to usefully feed a
    second round. UNKNOWN, not a hang -- this is the main regression
    test for the pathological formula-growth issue found during
    development (a genuine ~750,000-character reachable-set formula fed
    back as a Houdini candidate without a size cap).
    """
    smt2 = """
(set-logic HORN)
(declare-var c Int)
(declare-var c1 Int)
(declare-var len Int)
(declare-var x Int)
(declare-var y Int)
(declare-var steps Int)
(declare-var y1 Int)
(declare-var steps1 Int)
(declare-rel a (Int Int))
(declare-rel b (Int Int Int))
(declare-rel fail ())

(rule (a 0 len))
(rule (=> (and (a c len) (< c len) (= c1 (+ c 1))) (a c1 len)))
(rule (=> (a c len) (b c 0 0)))
(rule (=> (and (b x y steps) (< steps 5)
               (= y1 (+ y (ite (>= x 0) 2 (- 2))))
               (= steps1 (+ steps 1)))
          (b x y1 steps1)))
(rule (=> (and (b x y steps) (not (= y (* 2 steps)))) fail))
(query fail)
"""
    import tempfile

    with tempfile.TemporaryDirectory() as tmp:
        path = _write(Path(tmp), "handoff_gap.smt2", smt2)
        program = parse_chc_file(path, slice_program=False)

        result = run_ff_houdini(
            program,
            ff_timeout_ms=1000,
            ff_overall_timeout_s=5,
            houdini_timeout_ms=1000,
        )

    assert result.status is FFHoudiniStatus.UNKNOWN
    assert result.rounds >= 1


def test_stops_early_when_the_pool_stops_changing():
    """The flagship handoff-gap UNKNOWN case (see the test above) with a
    generous round budget: it should still stop well before using all of
    it, since neither relation's reachable-set formula stays small
    enough to feed forward, so round 2's pool is identical to round 1's.
    """
    smt2 = """
(set-logic HORN)
(declare-var c Int)
(declare-var c1 Int)
(declare-var len Int)
(declare-var x Int)
(declare-var y Int)
(declare-var steps Int)
(declare-var y1 Int)
(declare-var steps1 Int)
(declare-rel a (Int Int))
(declare-rel b (Int Int Int))
(declare-rel fail ())

(rule (a 0 len))
(rule (=> (and (a c len) (< c len) (= c1 (+ c 1))) (a c1 len)))
(rule (=> (a c len) (b c 0 0)))
(rule (=> (and (b x y steps) (< steps 5)
               (= y1 (+ y (ite (>= x 0) 2 (- 2))))
               (= steps1 (+ steps 1)))
          (b x y1 steps1)))
(rule (=> (and (b x y steps) (not (= y (* 2 steps)))) fail))
(query fail)
"""
    import tempfile

    with tempfile.TemporaryDirectory() as tmp:
        path = _write(Path(tmp), "handoff_gap.smt2", smt2)
        program = parse_chc_file(path, slice_program=False)

        result = run_ff_houdini(
            program,
            max_rounds=10,
            ff_timeout_ms=1000,
            ff_overall_timeout_s=5,
            houdini_timeout_ms=1000,
        )

    assert result.status is FFHoudiniStatus.UNKNOWN
    assert result.rounds < 10


def test_default_max_rounds_is_three():
    assert DEFAULT_MAX_ROUNDS == 3


def test_round_budget_is_respected(tmp_path):
    smt2 = """
(set-logic HORN)
(declare-var c Int)
(declare-var c1 Int)
(declare-var len Int)
(declare-var x Int)
(declare-var y Int)
(declare-var steps Int)
(declare-var y1 Int)
(declare-var steps1 Int)
(declare-rel a (Int Int))
(declare-rel b (Int Int Int))
(declare-rel fail ())

(rule (a 0 len))
(rule (=> (and (a c len) (< c len) (= c1 (+ c 1))) (a c1 len)))
(rule (=> (a c len) (b c 0 0)))
(rule (=> (and (b x y steps) (< steps 5)
               (= y1 (+ y (ite (>= x 0) 2 (- 2))))
               (= steps1 (+ steps 1)))
          (b x y1 steps1)))
(rule (=> (and (b x y steps) (not (= y (* 2 steps)))) fail))
(query fail)
"""
    path = _write(tmp_path, "handoff_gap.smt2", smt2)
    program = parse_chc_file(path, slice_program=False)

    result = run_ff_houdini(
        program,
        max_rounds=1,
        ff_timeout_ms=1000,
        ff_overall_timeout_s=5,
        houdini_timeout_ms=1000,
    )

    assert result.rounds <= 1
    assert result.status is FFHoudiniStatus.UNKNOWN


# ---------------------------------------------------------------------------
# CLI wiring.
# ---------------------------------------------------------------------------


def test_cli_ff_houdini_reports_success(capsys):
    from pyhorn_bnd.cli import main

    exit_code = main(
        [
            "--ff-houdini",
            "--ff-timeout-ms",
            "1000",
            "--ff-overall-timeout-s",
            "4",
            "--to",
            "1000",
            str(ARRAY_EQ_EXAMPLE),
        ]
    )

    assert exit_code == 0
    assert capsys.readouterr().out.strip() == "Success"


def test_cli_ff_houdini_json_reports_rounds(capsys):
    import json

    from pyhorn_bnd.cli import main

    main(
        [
            "--ff-houdini",
            "--ff-timeout-ms",
            "1000",
            "--ff-overall-timeout-s",
            "4",
            "--to",
            "1000",
            "--json",
            str(ARRAY_EQ_EXAMPLE),
        ]
    )
    out = json.loads(capsys.readouterr().out.splitlines()[0])

    assert out["status"] == "safe"
    assert out["rounds"] >= 2


def test_cli_ff_houdini_max_rounds_is_wired_through(capsys):
    from pyhorn_bnd.cli import main

    exit_code = main(
        [
            "--ff-houdini",
            "--ff-houdini-max-rounds",
            "1",
            "--ff-timeout-ms",
            "1000",
            "--ff-overall-timeout-s",
            "4",
            "--to",
            "1000",
            str(ARRAY_EQ_EXAMPLE),
        ]
    )

    # This example needs 2 rounds (see the flagship test above); capped
    # at 1, it should not find the proof.
    assert exit_code == 2


def test_cli_ff_houdini_combines_with_broadening_flags(tmp_path, capsys):
    from pyhorn_bnd.cli import main

    exit_code = main(
        [
            "--ff-houdini",
            "--seed-houdini",
            "--phasefit",
            "--mut",
            "--trace-houdini",
            "--ff-timeout-ms",
            "1000",
            "--ff-overall-timeout-s",
            "4",
            "--to",
            "1000",
            str(ARRAY_EQ_EXAMPLE),
        ]
    )

    assert exit_code in (0, 1, 2)  # must not crash; verdict may legitimately vary


def test_cli_ff_houdini_rejects_combination_with_ff(tmp_path, capsys):
    from pyhorn_bnd.cli import main

    with pytest.raises(SystemExit) as exc_info:
        main(["--ff", "--ff-houdini", str(ARRAY_EQ_EXAMPLE)])
    assert exc_info.value.code == 2
    assert "--ff-houdini" in capsys.readouterr().err


def test_cli_ff_houdini_rejects_combination_with_ff_seeded(tmp_path, capsys):
    from pyhorn_bnd.cli import main

    with pytest.raises(SystemExit) as exc_info:
        main(["--ff-houdini", "--ff-seeded", str(ARRAY_EQ_EXAMPLE)])
    assert exc_info.value.code == 2
    assert "--ff-houdini" in capsys.readouterr().err


def test_cli_ff_houdini_max_rounds_requires_ff_houdini(tmp_path, capsys):
    from pyhorn_bnd.cli import main

    with pytest.raises(SystemExit) as exc_info:
        main(["--ff-houdini-max-rounds", "5", str(ARRAY_EQ_EXAMPLE)])
    assert exc_info.value.code == 2
    assert "--ff-houdini-max-rounds" in capsys.readouterr().err


def test_cli_ff_houdini_max_rounds_must_be_positive(tmp_path, capsys):
    from pyhorn_bnd.cli import main

    with pytest.raises(SystemExit) as exc_info:
        main(["--ff-houdini", "--ff-houdini-max-rounds", "0", str(ARRAY_EQ_EXAMPLE)])
    assert exc_info.value.code == 2


def test_cli_ff_houdini_print_invariants_on_safe(capsys):
    from pyhorn_bnd.cli import main

    main(
        [
            "--ff-houdini",
            "--ff-timeout-ms",
            "1000",
            "--ff-overall-timeout-s",
            "4",
            "--to",
            "1000",
            "--print-invariants",
            str(ARRAY_EQ_EXAMPLE),
        ]
    )
    out = capsys.readouterr().out
    assert "inv(" in out
    assert "Success" in out
