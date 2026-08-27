"""Tests for :mod:`pyhorn_bnd.ff_houdini`.

See that module's docstring for the soundness argument behind feeding
forward-fixpoint's generalized fixpoint into Houdini's candidate pool,
and Houdini's own internally-stable candidates back into forward-fixpoint
as external invariants.
"""

from __future__ import annotations

from pathlib import Path

from pyhorn_bnd.ff_houdini import FFHoudiniStatus, run_ff_houdini
from pyhorn_bnd.horn import parse_chc_file

EXAMPLES = Path(__file__).resolve().parents[1] / "examples"


def _write(tmp_path: Path, name: str, smt2: str) -> Path:
    path = tmp_path / name
    path.write_text(smt2)
    return path


# ---------------------------------------------------------------------------
# The flagship case: a cross-relation handoff where the fact Houdini needs
# for inductiveness (x>=0, on relation b) has no literal comparison atom
# anywhere for SeedMiner to weaken -- it only exists because a's own value
# (itself weakenable from a's fact rule) is copied across a relation
# boundary via argument position, not asserted directly. Forward-fixpoint's
# reachability computation (which propagates real formulas across
# relations, not just syntax) finds it where syntactic mining structurally
# cannot. Verified: --ff alone and --seed-houdini alone (no --trace-houdini)
# both report unknown/unknown on this input; --seed-houdini combined with
# --trace-houdini also happens to succeed (a different, more expensive
# technique with its own reach), which is fine -- it doesn't take away
# from what --ff alone and --seed-houdini alone, specifically, cannot do.
# ---------------------------------------------------------------------------

_HANDOFF_GAP_SMT2 = """
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


def test_ff_alone_and_seed_houdini_alone_both_fail_on_the_gap_example(tmp_path):
    """Ground truth for the flagship case below: confirms neither
    component alone can prove this input safe, so the SAFE verdict
    the combined test asserts is actually demonstrating something,
    not just re-deriving what one side already had on its own.
    """
    from pyhorn_bnd.forward_fixpoint import ForwardFixpointStatus, run_forward_fixpoint
    from pyhorn_bnd.houdini import HoudiniStatus, run_seed_houdini

    path = _write(tmp_path, "handoff_gap.smt2", _HANDOFF_GAP_SMT2)
    program = parse_chc_file(path, slice_program=False)

    ff_only = run_forward_fixpoint(program)
    assert ff_only.status is ForwardFixpointStatus.UNKNOWN

    seed_only = run_seed_houdini(program)
    assert seed_only.status is HoudiniStatus.UNKNOWN


def test_combined_succeeds_where_ff_alone_and_seed_houdini_alone_both_fail(
    tmp_path,
):
    """The flagship positive case: forward-fixpoint's generalized track
    finds `x>=0` for relation `b` (confirmed via
    `result.generalized_invariant` containing it in isolation), purely
    from propagating `a`'s own (separately, syntactically-derivable)
    invariant across the handoff rule -- something SeedMiner's per-clause
    atom weakening cannot do, since the handoff rule has no literal
    comparison on `b`'s first argument at all. Feeding that fact into
    Houdini's candidate pool is enough for its own syntactically-mined
    `y == 2*steps` (harvestable directly from the negated query) to
    become provably inductive.
    """
    path = _write(tmp_path, "handoff_gap.smt2", _HANDOFF_GAP_SMT2)
    program = parse_chc_file(path, slice_program=False)

    result = run_ff_houdini(program, use_trace=False, max_rounds=3)

    assert result.status is FFHoudiniStatus.SAFE
    assert result.invariants is not None


# ---------------------------------------------------------------------------
# Delegation: run_ff_houdini must faithfully pass through whichever
# component actually settles the question, without altering the verdict.
# ---------------------------------------------------------------------------


def test_delegates_to_forward_fixpoint_safe_without_needing_houdini(tmp_path):
    smt2 = """
(declare-var x Int)
(declare-rel inv (Int))
(declare-rel fail ())
(rule (inv 0))
(rule (=> (and (inv x) (< x 5)) (inv (+ x 1))))
(rule (=> (and (inv x) (>= x 10)) fail))
(query fail)
"""
    path = _write(tmp_path, "bounded_safe.smt2", smt2)
    program = parse_chc_file(path, slice_program=False)

    result = run_ff_houdini(program)

    assert result.status is FFHoudiniStatus.SAFE
    assert result.rounds == 1
    assert "forward-fixpoint" in result.message


def test_delegates_to_forward_fixpoint_unsafe(tmp_path):
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


def test_delegates_to_houdini_success_when_ff_has_nothing_to_add(tmp_path):
    """A relational fact (y == 2*x) that plain seed-mining already finds
    unaided from the negated query -- forward-fixpoint's generalized
    track can't establish this on its own (it drops the x/y
    correlation), so this round should still resolve via Houdini,
    with an empty (or absent) contribution from forward-fixpoint.
    """
    smt2 = """
(set-logic HORN)
(declare-var x Int)
(declare-var y Int)
(declare-var len Int)
(declare-var x1 Int)
(declare-var y1 Int)
(declare-rel inv (Int Int Int))
(declare-rel fail ())
(rule (inv 0 0 len))
(rule (=> (and (inv x y len) (< x len) (= x1 (+ x 1)) (= y1 (+ y 2))) (inv x1 y1 len)))
(rule (=> (and (inv x y len) (not (= y (* 2 x)))) fail))
(query fail)
"""
    path = _write(tmp_path, "relational.smt2", smt2)
    program = parse_chc_file(path, slice_program=False)

    result = run_ff_houdini(program)

    assert result.status is FFHoudiniStatus.SAFE
    assert "Houdini" in result.message


# ---------------------------------------------------------------------------
# Genuinely unprovable-by-either input: must terminate with UNKNOWN, not
# loop forever or raise.
# ---------------------------------------------------------------------------


def test_terminates_within_max_rounds_regardless_of_outcome(tmp_path):
    """Whatever the eventual verdict, the round budget must be a hard
    cap -- never loop past it, whether that's because a proof was
    found early or because neither side ever helps.
    """
    smt2 = """
(declare-var x Int)
(declare-rel inv (Int))
(declare-rel fail ())
(rule (inv 0))
(rule (=> (inv x) (inv (+ x 1))))
(rule (=> (and (inv x) (>= x 1000000)) fail))
(query fail)
"""
    path = _write(tmp_path, "far_off_query.smt2", smt2)
    program = parse_chc_file(path, slice_program=False)

    result = run_ff_houdini(program, max_rounds=2, ff_max_iterations=3)

    assert result.rounds <= 2


def test_max_rounds_is_respected(tmp_path):
    """Even a trivially-unprovable input (needs modular reasoning
    neither side has) must never exceed max_rounds -- reusing the
    dillig46 case with a tighter cap than the test above.
    """
    smt2 = """
(declare-rel inv (Int Int Int Int))
(declare-var x0 Int)
(declare-var x1 Int)
(declare-var y0 Int)
(declare-var y1 Int)
(declare-var z0 Int)
(declare-var z1 Int)
(declare-var w0 Int)
(declare-var w1 Int)
(declare-var tmp0 Int)
(declare-var tmp1 Int)
(declare-rel fail ())
(rule (=> (and (= x1 0) (= y1 0) (= z1 0) (= w1 1)) (inv x1 y1 z1 w1)))
(rule (=>
    (and
        (inv x0 y0 z0 w0)
        (= tmp0 (mod w0 2))
        (= tmp1 (mod z0 2))
        (= x1 (ite (= tmp0 1) (+ x0 1) x0))
        (= w1 (ite (= tmp0 1) (+ w0 1) w0))
        (= y1 (ite (= tmp1 0) (+ y0 1) y0))
        (= z1 (ite (= tmp1 0) (+ z0 1) z0))
    )
    (inv x1 y1 z1 w1)
  )
)
(rule (=> (and (inv x0 y0 z0 w0) (not (<= x0 1))) fail))
(query fail)
"""
    path = _write(tmp_path, "trivially_unknown.smt2", smt2)
    program = parse_chc_file(path, slice_program=False)

    result = run_ff_houdini(program, max_rounds=1, ff_timeout_ms=200)

    assert result.rounds <= 1
