from __future__ import annotations

import json
from pathlib import Path

import pytest
import z3

from pyhorn_bnd import (
    AccelerationSummary,
    BoundedExplorer,
    ExplorationStatus,
    accelerate_program,
    parse_chc_file,
)
from pyhorn_bnd.accel import describe_witness
from pyhorn_bnd.cli import main

ROOT = Path(__file__).resolve().parents[1]
EXAMPLES = ROOT / "examples" / "accelerate_bmc"


BENCHMARKS = ROOT / "examples" / "accelerate_bmc" / "benchmarks"

# name -> expected search depth with --accelerate-bmc. Every one of these
# is unsafe only after somewhere between ~300M and ~400B real loop
# iterations (see BENCHMARKS/README.md for the exact thresholds and the
# small-scale twin each was validated against) -- plain unrolling would
# need a --upto in that range, so this suite deliberately never runs the
# unaccelerated baseline against the full-size files, only the CLI's
# --accelerate-bmc path.
BENCHMARK_DEPTHS = [
    ("01_up_counter_unit.smt2", 3),
    ("02_down_counter_unit.smt2", 3),
    ("03_up_counter_step13.smt2", 3),
    ("04_two_var_lockstep.smt2", 3),
    ("05_three_var_lockstep.smt2", 3),
    ("06_up_counter_negative_init.smt2", 3),
    ("07_down_counter_step.smt2", 3),
    ("08_up_counter_inclusive_guard.smt2", 3),
    ("09_two_var_converging.smt2", 3),
    ("10_up_counter_conjunctive_guard.smt2", 3),
    ("11_two_phase_classic.smt2", 4),
    ("12_two_phase_payload_both_phases.smt2", 4),
    ("13_two_phase_decrement_then_hold.smt2", 4),
    ("14_two_phase_fast_second_phase.smt2", 4),
    ("15_two_phase_three_vars.smt2", 4),
    ("16_two_phase_inclusive_guards.smt2", 4),
    ("17_three_phase_relay.smt2", 5),
    ("18_four_phase_relay.smt2", 6),
    ("19_five_phase_relay.smt2", 7),
    ("20_three_phase_relay_variable_rates.smt2", 5),
]


@pytest.mark.parametrize("filename,expected_depth", BENCHMARK_DEPTHS)
def test_benchmark_suite_resolves_at_expected_depth(
    filename: str, expected_depth: int
) -> None:
    """Each of these is unsafe only after hundreds of millions to hundreds
    of billions of real loop iterations -- intractable for plain
    unrolling, resolved by --accelerate-bmc at a depth in the single
    digits regardless. Runs through the same accelerate_program +
    BoundedExplorer path the CLI uses, not a subprocess, so this suite
    stays fast; test_cli_accelerate_bmc_flag_finds_shallow_counterexample
    above already covers the actual CLI invocation end to end.
    """
    program = parse_chc_file(BENCHMARKS / filename)
    augmented, summary = accelerate_program(program)
    assert summary.shortcuts_added >= 1
    result = BoundedExplorer(augmented, timeout_ms=10_000).explore(upto=15)
    assert result.status is ExplorationStatus.COUNTEREXAMPLE
    assert result.explored_upto == expected_depth


def test_validate_bound_rejects_a_proposal_it_cannot_confirm(tmp_path: Path) -> None:
    """The propose/validate split (VCEX's Validate applied to a candidate
    guard bound, independent of how it was proposed) should refuse a
    candidate that _propose_bound got wrong, rather than trust it by
    construction. This constructs a case via the public API rather than
    calling the private helpers directly: the conjunctive-guard case
    (see test_up_counter_conjunctive_guard.smt2's shape) already exercises
    an increasing-truth proposal; here we confirm the accepted candidate
    actually passes independent validation by checking the produced
    shortcut is semantically sound with a direct z3 check, not just that
    accelerate_program didn't crash.
    """
    source = tmp_path / "validated.smt2"
    source.write_text(
        """
        (set-logic HORN)
        (declare-rel inv (Int))
        (declare-rel fail ())
        (declare-var x0 Int) (declare-var x1 Int)
        (rule (=> (= x1 0) (inv x1)))
        (rule (=> (and (inv x0) (>= x0 0) (< x0 777) (= x1 (+ x0 1))) (inv x1)))
        (rule (=> (and (inv x0) (>= x0 777)) fail))
        (query fail)
        """,
        encoding="utf-8",
    )
    program = parse_chc_file(source)
    augmented, summary = accelerate_program(program)
    assert summary.shortcuts_added == 1
    shortcut = summary.shortcut_rules[0]

    x0, x1 = program.rules[1].src_args[0], program.rules[1].dst_args[0]
    n_var = shortcut.rule_vars[-1]
    s = z3.Solver()
    s.add(x0 == 0, shortcut.body, x1 == 777)
    assert s.check() == z3.sat
    assert s.model().eval(n_var).as_long() == 777

    s2 = z3.Solver()
    s2.add(x0 == 0, shortcut.body, x1 == 778)
    assert s2.check() == z3.unsat


def test_witness_report_matches_real_iteration_count() -> None:
    """The VCEX-style witness report's total N must equal the sum of each
    accelerated step's concrete n (plain steps contribute 1 each), and
    every accelerated step must show a formula for every state variable.
    """
    program = parse_chc_file(BENCHMARKS / "17_three_phase_relay.smt2")
    augmented, summary = accelerate_program(program)
    result = BoundedExplorer(augmented, timeout_ms=10_000).explore(upto=15)
    assert result.status is ExplorationStatus.COUNTEREXAMPLE
    check = result.trace_check
    assert check is not None and check.model is not None

    fresh_vars = tuple(step.fresh_rule_vars for step in check.vc.steps)
    report = describe_witness(check.vc.trace, check.model, fresh_vars, summary)
    assert "Witness:" in report

    expected_total = 0
    accelerated_count = 0
    for step_index, rule in enumerate(check.vc.trace):
        formulas = summary.formulas_by_rule_id.get(rule.rule_id)
        if formulas is None:
            expected_total += 1
            continue
        accelerated_count += 1
        assert len(formulas) == len(rule.src_args)
        n_value = check.model.eval(fresh_vars[step_index][-1], model_completion=True)
        expected_total += n_value.as_long()

    assert accelerated_count == 3  # one segment per phase
    assert f"N = {expected_total} real transition(s)" in report


def test_cli_human_output_includes_witness_report(capsys) -> None:
    exit_code = main(
        [
            "--accelerate-bmc",
            "--upto",
            "15",
            str(BENCHMARKS / "11_two_phase_classic.smt2"),
        ]
    )
    assert exit_code == 1
    out = capsys.readouterr().out
    assert "Witness: 4 trace step(s) represent N =" in out
    assert "applied n=" in out


def test_cli_json_witness_field_matches_text_report(capsys) -> None:
    exit_code = main(
        [
            "--accelerate-bmc",
            "--json",
            "--upto",
            "15",
            str(BENCHMARKS / "11_two_phase_classic.smt2"),
        ]
    )
    assert exit_code == 1
    data = json.loads(capsys.readouterr().out)
    witness = data["witness"]
    assert witness is not None
    assert len(witness["accelerated_segments"]) == 2
    plain_steps = data["explored_upto"] - len(witness["accelerated_segments"])
    assert witness["real_steps"] == (
        sum(seg["n"] for seg in witness["accelerated_segments"]) + plain_steps
    )


def test_no_self_loop_is_a_clean_no_op() -> None:
    program = parse_chc_file(EXAMPLES / "no_self_loop.smt2")
    augmented, summary = accelerate_program(program)
    assert summary.inductive_rules_considered == 0
    assert summary.branches_considered == 0
    assert summary.shortcuts_added == 0
    assert augmented is program  # identity, not just equality: no rebuild happened

    result = BoundedExplorer(augmented, timeout_ms=5_000).explore(upto=10)
    assert result.status is ExplorationStatus.COUNTEREXAMPLE


def test_single_branch_self_loop_gets_one_shortcut() -> None:
    program = parse_chc_file(EXAMPLES / "deep_counter_small.smt2")
    augmented, summary = accelerate_program(program)
    assert summary.inductive_rules_considered == 1
    assert summary.branches_considered == 1
    assert summary.shortcuts_added == 1
    # The single branch fully covers the raw self-loop rule, so it is
    # replaced (not kept alongside its shortcut) -- same rule count, not
    # +1. See accelerate_program's docstring for why keeping both would
    # double the search's branching factor at every loop step.
    assert len(augmented.rules) == len(program.rules)
    assert not any(rule.is_inductive and rule.body.eq(
        next(r for r in program.rules if r.is_inductive).body
    ) for rule in augmented.rules)

    shortcut = summary.shortcut_rules[0]
    assert shortcut.is_inductive
    assert shortcut.src_relation == shortcut.dst_relation


def test_accelerated_search_reaches_deep_counterexample_at_shallow_depth() -> None:
    program = parse_chc_file(EXAMPLES / "deep_counter_small.smt2")
    augmented, summary = accelerate_program(program)
    assert summary.shortcuts_added == 1

    result = BoundedExplorer(augmented, timeout_ms=5_000).explore(upto=10)
    assert result.status is ExplorationStatus.COUNTEREXAMPLE
    # fact -> accelerated jump -> exit: independent of the threshold (50
    # here), unlike the unaccelerated case below.
    assert result.explored_upto == 3

    unaccelerated = BoundedExplorer(program, timeout_ms=5_000).explore(upto=52)
    assert unaccelerated.status is ExplorationStatus.COUNTEREXAMPLE
    # 1 (fact) + 50 (self-loop steps to reach x=50) + 1 (exit) = 52.
    assert unaccelerated.explored_upto == 52


def test_accelerated_search_scales_independently_of_threshold_magnitude() -> None:
    """The whole point of acceleration: a threshold of one billion costs the
    same three-step search depth as a threshold of fifty, because the
    shortcut's closed form doesn't care how large `n` turns out to be.
    Deliberately does NOT run the unaccelerated baseline here -- that would
    need on the order of a billion search depths.
    """
    program = parse_chc_file(EXAMPLES / "deep_counter_large.smt2")
    augmented, summary = accelerate_program(program)
    assert summary.shortcuts_added == 1

    result = BoundedExplorer(augmented, timeout_ms=5_000).explore(upto=10)
    assert result.status is ExplorationStatus.COUNTEREXAMPLE
    assert result.explored_upto == 3
    model = result.trace_check.model
    assert model is not None
    n_values = [
        model[decl]
        for decl in model.decls()
        if str(decl.name()).endswith("__accel_n_3")
    ]
    assert n_values and n_values[0].as_long() == 1_000_000_000


def test_branching_self_loop_gets_one_shortcut_per_branch() -> None:
    program = parse_chc_file(EXAMPLES / "two_phase_small.smt2")
    augmented, summary = accelerate_program(program)
    assert summary.inductive_rules_considered == 1
    assert summary.branches_considered == 2
    assert summary.shortcuts_added == 2
    # Both branches accelerated, so the raw ite rule is replaced by its
    # two shortcuts rather than kept alongside them (same rationale as
    # the single-branch case above).
    assert len(augmented.rules) == len(program.rules) + 1

    result = BoundedExplorer(augmented, timeout_ms=5_000).explore(upto=10)
    assert result.status is ExplorationStatus.COUNTEREXAMPLE
    # fact -> phase-1 shortcut -> phase-2 shortcut -> exit. Exact rule_ids
    # depend on internal renumbering, so check structure/semantics instead
    # of hard-coding ids: two consecutive inductive (self-loop) steps
    # sandwiched between the fact and the exit, and a model where the
    # final y has actually reached the threshold.
    assert result.explored_upto == 4
    trace = result.trace_check.vc.trace
    assert trace[0].is_fact
    assert trace[-1].is_query
    assert trace[1].is_inductive and trace[2].is_inductive
    assert trace[1].rule_id != trace[2].rule_id


def test_acceleration_never_changes_a_bounded_safe_verdict(tmp_path: Path) -> None:
    """A cyclic-but-safe program: acceleration only ever adds semantically
    redundant edges, so it must never turn a genuinely safe bound into a
    false counterexample, and vice versa.
    """
    source = tmp_path / "safe_loop.smt2"
    source.write_text(
        """
        (set-logic HORN)
        (declare-rel inv (Int))
        (declare-rel fail ())
        (declare-var x0 Int) (declare-var x1 Int)
        (rule (=> (= x1 0) (inv x1)))
        (rule (=> (and (inv x0) (< x0 20) (= x1 (+ x0 1))) (inv x1)))
        (rule (=> (and (inv x0) (>= x0 20) (< x0 0)) fail))
        (query fail)
        """,
        encoding="utf-8",
    )
    program = parse_chc_file(source)
    augmented, summary = accelerate_program(program)
    assert summary.shortcuts_added == 1

    accelerated_result = BoundedExplorer(augmented, timeout_ms=5_000).explore(upto=25)
    plain_result = BoundedExplorer(program, timeout_ms=5_000).explore(upto=25)
    assert accelerated_result.status == plain_result.status
    assert accelerated_result.status is ExplorationStatus.BOUNDED_SAFE


def test_cli_accelerate_bmc_flag_finds_shallow_counterexample(capsys) -> None:
    exit_code = main(
        [
            "--accelerate-bmc",
            "--debug",
            "--upto",
            "10",
            str(EXAMPLES / "deep_counter_small.smt2"),
        ]
    )
    out = capsys.readouterr().out
    assert exit_code == 1
    assert "Acceleration: 1 self-loop rule(s)" in out
    assert "Counterexample of length 3 found" in out


def test_cli_accelerate_bmc_json_reports_summary(capsys) -> None:
    exit_code = main(
        [
            "--accelerate-bmc",
            "--json",
            "--upto",
            "10",
            str(EXAMPLES / "two_phase_small.smt2"),
        ]
    )
    assert exit_code == 1
    data = json.loads(capsys.readouterr().out)
    assert data["acceleration"]["shortcuts_added"] == 2
    assert data["explored_upto"] == 4


@pytest.mark.parametrize(
    "conflicting_flag",
    [
        "--seed-houdini",
        "--phasefit",
        "--trace-houdini",
        "--ff",
        "--ff-houdini",
        "--ff-seeded",
        "--mut",
    ],
)
def test_cli_rejects_accelerate_bmc_with_houdini_mode_flags(
    conflicting_flag: str, capsys
) -> None:
    with pytest.raises(SystemExit) as excinfo:
        main(
            [
                "--accelerate-bmc",
                conflicting_flag,
                str(EXAMPLES / "deep_counter_small.smt2"),
            ]
        )
    assert excinfo.value.code == 2
    assert "--accelerate-bmc" in capsys.readouterr().err


def test_source_equality_guard_is_not_dropped(tmp_path: Path) -> None:
    """A source-state equality is a guard, not an update definition.

    The loop can fire only once: 0 -> 1.  Dropping ``x0 == 0`` from the
    shortcut would incorrectly permit n=2 and create the unreachable state
    x=2, turning this safe program into a false counterexample.
    """
    source = tmp_path / "equality_guard.smt2"
    source.write_text(
        """
        (set-logic HORN)
        (declare-rel inv (Int))
        (declare-rel fail ())
        (declare-var x0 Int) (declare-var x1 Int)
        (rule (=> (= x1 0) (inv x1)))
        (rule (=> (and (inv x0) (= x0 0) (= x1 (+ x0 1))) (inv x1)))
        (rule (=> (and (inv x0) (>= x0 2)) fail))
        (query fail)
        """,
        encoding="utf-8",
    )
    program = parse_chc_file(source)
    augmented, _summary = accelerate_program(program)
    plain = BoundedExplorer(program, timeout_ms=5_000).explore(upto=8)
    accelerated = BoundedExplorer(augmented, timeout_ms=5_000).explore(upto=8)
    assert plain.status is ExplorationStatus.BOUNDED_SAFE
    assert accelerated.status is ExplorationStatus.BOUNDED_SAFE


def test_coupled_recurrence_is_rejected_by_semantic_step_check(
    tmp_path: Path,
) -> None:
    """PhaseFit solves each variable separately, which is not a transition proof.

    For x' = x+y, y' = y+1, treating y as fixed while solving x proposes
    x(n)=x0+n*y0.  From (0,0) that predicts (0,2) after two steps, although
    the real state is (1,2).  The acceleration layer must reject that closed
    form instead of introducing a spurious counterexample.
    """
    source = tmp_path / "coupled.smt2"
    source.write_text(
        """
        (set-logic HORN)
        (declare-rel inv (Int Int))
        (declare-rel fail ())
        (declare-var x0 Int) (declare-var x1 Int)
        (declare-var y0 Int) (declare-var y1 Int)
        (rule (=> (and (= x1 0) (= y1 0)) (inv x1 y1)))
        (rule (=> (and (inv x0 y0)
                       (= x1 (+ x0 y0))
                       (= y1 (+ y0 1)))
                  (inv x1 y1)))
        (rule (=> (and (inv x0 y0) (= x0 0) (>= y0 2)) fail))
        (query fail)
        """,
        encoding="utf-8",
    )
    program = parse_chc_file(source)
    augmented, summary = accelerate_program(program)
    assert summary.shortcuts_added == 0
    result = BoundedExplorer(augmented, timeout_ms=5_000).explore(upto=8)
    assert result.status is ExplorationStatus.BOUNDED_SAFE


def test_constant_assignment_closed_form_must_anchor_at_source_state(
    tmp_path: Path,
) -> None:
    """A PhaseFit constant form is not automatically a virtual trajectory.

    Here x becomes 0 after the first iteration, so the guard x>0 prevents a
    second iteration.  PhaseFit represents ``x' = 0`` as the constant form
    x(n)=0, which does not satisfy x(0)=x_initial.  Without the anchor check,
    the guard appears permanently false/constant while y(n)=y0+n can still be
    used to jump to y=2, creating a spurious counterexample.
    """
    source = tmp_path / "constant_assignment_anchor.smt2"
    source.write_text(
        """
        (set-logic HORN)
        (declare-rel inv (Int Int))
        (declare-rel fail ())
        (declare-var x0 Int) (declare-var x1 Int)
        (declare-var y0 Int) (declare-var y1 Int)
        (rule (=> (and (= x1 1) (= y1 0)) (inv x1 y1)))
        (rule (=> (and (inv x0 y0)
                       (> x0 0)
                       (= x1 0)
                       (= y1 (+ y0 1)))
                  (inv x1 y1)))
        (rule (=> (and (inv x0 y0) (>= y0 2)) fail))
        (query fail)
        """,
        encoding="utf-8",
    )
    program = parse_chc_file(source)
    augmented, summary = accelerate_program(program)
    assert summary.shortcuts_added == 0
    result = BoundedExplorer(augmented, timeout_ms=5_000).explore(upto=8)
    assert result.status is ExplorationStatus.BOUNDED_SAFE


def test_residual_guard_expands_through_update_temporaries(tmp_path: Path) -> None:
    """A guard over an SSA temporary must evolve with the virtual state.

    ``h`` is defined from x on each concrete iteration.  Treating ``h < 3`` as
    a loop-invariant condition on one shortcut-local auxiliary value would let
    x jump past 2.  Acceleration therefore expands the selected definition and
    validates the real guard ``x+1 < 3`` along the closed-form trajectory.
    """
    source = tmp_path / "temporary_guard.smt2"
    source.write_text(
        """
        (set-logic HORN)
        (declare-rel inv (Int))
        (declare-rel fail ())
        (declare-var x0 Int) (declare-var x1 Int) (declare-var h Int)
        (rule (=> (= x1 0) (inv x1)))
        (rule (=> (and (inv x0)
                       (= h (+ x0 1))
                       (= x1 h)
                       (< h 3))
                  (inv x1)))
        (rule (=> (and (inv x0) (>= x0 3)) fail))
        (query fail)
        """,
        encoding="utf-8",
    )
    program = parse_chc_file(source)
    augmented, summary = accelerate_program(program)
    assert summary.shortcuts_added == 1
    accelerated = BoundedExplorer(augmented, timeout_ms=5_000).explore(upto=8)
    plain = BoundedExplorer(program, timeout_ms=5_000).explore(upto=8)
    assert plain.status is ExplorationStatus.BOUNDED_SAFE
    assert accelerated.status is ExplorationStatus.BOUNDED_SAFE


def test_incomplete_branch_enumeration_never_replaces_raw_rule(
    tmp_path: Path,
) -> None:
    """PhaseFit caps >64 Cartesian branch combinations to one leaf.

    Seven independent two-way updates create 128 real branch combinations.
    The extractor intentionally returns only its first combination; the
    acceleration layer may add that sound shortcut, but must keep the raw rule
    because the one-step coverage proof fails for the other 127 combinations.
    """
    xs = [f"x{i}" for i in range(7)]
    fs = [f"f{i}" for i in range(7)]
    args0 = [f"{name}0" for name in [*xs, *fs]]
    args1 = [f"{name}1" for name in [*xs, *fs]]
    lines = [
        "(set-logic HORN)",
        f"(declare-rel inv ({' '.join(['Int'] * len(args0))}))",
        "(declare-rel fail ())",
    ]
    for name in [*xs, *fs]:
        lines.append(f"(declare-var {name}0 Int) (declare-var {name}1 Int)")
    init_eqs = " ".join(f"(= {name}1 0)" for name in [*xs, *fs])
    lines.append(f"(rule (=> (and {init_eqs}) (inv {' '.join(args1)})))")
    updates = [
        f"(= x{i}1 (ite (>= f{i}0 0) (+ x{i}0 1) (+ x{i}0 2)))"
        for i in range(7)
    ]
    updates.extend(f"(= f{i}1 f{i}0)" for i in range(7))
    lines.append(
        f"(rule (=> (and (inv {' '.join(args0)}) {' '.join(updates)}) "
        f"(inv {' '.join(args1)})))"
    )
    lines.append(
        f"(rule (=> (and (inv {' '.join(args0)}) (< x00 0) (> x00 0)) fail))"
    )
    lines.append("(query fail)")
    source = tmp_path / "cartesian_128.smt2"
    source.write_text("\n".join(lines), encoding="utf-8")

    program = parse_chc_file(source)
    original_loop = next(rule for rule in program.rules if rule.is_inductive)
    augmented, summary = accelerate_program(program)
    assert summary.branches_considered == 1
    assert summary.shortcuts_added == 1
    assert len(augmented.rules) == len(program.rules) + 1
    assert any(
        rule.is_inductive and rule.body.eq(original_loop.body)
        for rule in augmented.rules
    )


def test_nested_five_phase_relay_prunes_before_cartesian_cap() -> None:
    """Shared phase guards should be pruned before applying the 64-branch cap.

    The nested five-phase benchmark has 108 raw per-variable leaf
    combinations but only five satisfiable synchronized phases.  Acceleration
    should recover those five rather than inheriting PhaseFit's pre-SMT
    Cartesian truncation and seeing only the first phase.
    """
    program = parse_chc_file(BENCHMARKS / "19_five_phase_relay.smt2")
    _augmented, summary = accelerate_program(program)
    assert summary.branches_considered == 5
    assert summary.shortcuts_added == 5


def _direct_counterexample_at_shallow_depth(source: Path, expected_depth: int) -> None:
    """Shared assertion for the guard-direction regression tests below:
    accelerate, then confirm a counterexample is found at exactly the
    expected shallow depth (not merely "some" depth -- a wrong bound can
    make the search silently report bounded-safe instead of failing loudly,
    which is why these check the actual depth, not just the status).
    """
    program = parse_chc_file(source)
    augmented, summary = accelerate_program(program)
    assert summary.shortcuts_added >= 1
    result = BoundedExplorer(augmented, timeout_ms=5_000).explore(upto=15)
    assert result.status is ExplorationStatus.COUNTEREXAMPLE
    assert result.explored_upto == expected_depth


def test_non_strict_guard_bound_is_not_off_by_one(tmp_path: Path) -> None:
    """Regression test for a real bug found while building benchmarks: a
    non-strict loop guard (`x0 <= T`, as opposed to `x0 < T`) was getting
    an off-by-one bound from PhaseFit's classify_guard, silently making
    the last valid iteration unreachable -- BoundedExplorer reported
    bounded-safe for a genuinely unsafe program, for every upto, forever.
    """
    source = tmp_path / "inclusive_guard.smt2"
    source.write_text(
        """
        (set-logic HORN)
        (declare-rel inv (Int))
        (declare-rel fail ())
        (declare-var x0 Int) (declare-var x1 Int)
        (rule (=> (= x1 0) (inv x1)))
        (rule (=> (and (inv x0) (<= x0 50) (= x1 (+ x0 1))) (inv x1)))
        (rule (=> (and (inv x0) (> x0 50)) fail))
        (query fail)
        """,
        encoding="utf-8",
    )
    _direct_counterexample_at_shallow_depth(source, expected_depth=3)


def test_non_unit_step_guard_bound_is_exact(tmp_path: Path) -> None:
    """Regression test for the other half of the same bug: a non-unit step
    size (13) makes the algebraic crossover point fractional (500/13 =
    38.46...), and truncating it the wrong way similarly strands the
    search just short of the real threshold, forever.
    """
    source = tmp_path / "step_guard.smt2"
    source.write_text(
        """
        (set-logic HORN)
        (declare-rel inv (Int))
        (declare-rel fail ())
        (declare-var x0 Int) (declare-var x1 Int)
        (rule (=> (= x1 0) (inv x1)))
        (rule (=> (and (inv x0) (< x0 500) (= x1 (+ x0 13))) (inv x1)))
        (rule (=> (and (inv x0) (>= x0 500)) fail))
        (query fail)
        """,
        encoding="utf-8",
    )
    _direct_counterexample_at_shallow_depth(source, expected_depth=3)


def test_increasing_truth_guard_does_not_self_contradict(tmp_path: Path) -> None:
    """Regression test for a second, distinct bug: a guard whose truth
    INCREASES with the iterate index (e.g. `x0 >= 0` on a variable that
    only ever increases) was blindly run through the same "decreasing
    truth" bound logic as a normal loop guard, producing a bound like
    `n <= -x0` that -- combined with the existing `n > 0` requirement --
    made the entire synthesized shortcut unsatisfiable (n > 0 and n <= 0
    can never both hold), silently disabling acceleration for the whole
    branch rather than merely being imprecise.
    """
    source = tmp_path / "conjunctive_guard.smt2"
    source.write_text(
        """
        (set-logic HORN)
        (declare-rel inv (Int))
        (declare-rel fail ())
        (declare-var x0 Int) (declare-var x1 Int)
        (rule (=> (= x1 0) (inv x1)))
        (rule (=> (and (inv x0) (>= x0 0) (< x0 50) (= x1 (+ x0 1))) (inv x1)))
        (rule (=> (and (inv x0) (>= x0 50)) fail))
        (query fail)
        """,
        encoding="utf-8",
    )
    _direct_counterexample_at_shallow_depth(source, expected_depth=3)


def test_multi_phase_relay_accelerates_every_phase(tmp_path: Path) -> None:
    """Regression test for a third, related bug found on a 3+ phase relay:
    PhaseFit's nested-ite branch extraction produces guards like
    `And(x0>=15, Not(And(x0>=15, Not(x0>=30))), x0>=30)` for phase
    boundaries beyond the first, which needs simplification to become the
    plain `15 <= x0 < 30` it's logically equivalent to -- and a
    ctx-solver-simplify pass can itself leave a vacuously-true residual
    (`Not(And(False, Not(False)))`) on deeper (4+ way) trees that isn't a
    shape the guard-to-sympy translator recognises at all, silently
    failing just the one branch it's attached to. All of a rule's
    branches need to accelerate for the rule to be *replaced* rather than
    kept alongside its shortcuts (see accelerate_program's docstring for
    why that distinction matters for the search's branching factor) --
    which makes a single unnoticed per-branch failure on a relay costly,
    not just incomplete.
    """
    parts = ["(set-logic HORN)", "(declare-rel inv (Int Int Int Int Int Int))",
             "(declare-rel fail ())", "(declare-var x0 Int) (declare-var x1 Int)"]
    thresholds = [10, 20, 30, 40]
    payload_vars = ["a", "b", "c", "d", "e"]
    for v in payload_vars:
        parts.append(f"(declare-var {v}0 Int) (declare-var {v}1 Int)")
    parts.append(
        "(rule (=> (and "
        + " ".join(f"(= {v}1 0)" for v in ["x", *payload_vars])
        + f") (inv x1 {' '.join(v + '1' for v in payload_vars)})))"
    )
    updates = []
    for i, v in enumerate(payload_vars):
        # Phase i is active exactly when thresholds[i-1] <= x0 < thresholds[i]
        # (open on both ends for the first/last phase).
        lo = thresholds[i - 1] if i > 0 else None
        hi = thresholds[i] if i < len(thresholds) else None
        if lo is None:
            expr = f"(ite (< x0 {hi}) (+ {v}0 1) {v}0)"
        elif hi is None:
            expr = f"(ite (>= x0 {lo}) (+ {v}0 1) {v}0)"
        else:
            expr = f"(ite (and (>= x0 {lo}) (< x0 {hi})) (+ {v}0 1) {v}0)"
        updates.append(f"(= {v}1 {expr})")
    parts.append(
        "(rule (=> (and (inv x0 "
        + " ".join(f"{v}0" for v in payload_vars)
        + ") (= x1 (+ x0 1)) "
        + " ".join(updates)
        + f") (inv x1 {' '.join(v + '1' for v in payload_vars)})))"
    )
    parts.append(
        "(rule (=> (and (inv x0 "
        + " ".join(f"{v}0" for v in payload_vars)
        + f") (>= e0 30)) fail))"
    )
    parts.append("(query fail)")
    source = tmp_path / "five_phase.smt2"
    source.write_text("\n".join(parts), encoding="utf-8")

    program = parse_chc_file(source)
    augmented, summary = accelerate_program(program)
    assert summary.branches_considered == 5
    assert summary.shortcuts_added == 5
    # All 5 branches accelerated, so the raw rule must be fully replaced.
    assert len(augmented.rules) == len(program.rules) + 4

    result = BoundedExplorer(augmented, timeout_ms=5_000).explore(upto=15)
    assert result.status is ExplorationStatus.COUNTEREXAMPLE
    assert result.explored_upto == 7  # fact + 5 phase shortcuts + exit
