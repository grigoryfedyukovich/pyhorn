from __future__ import annotations

from pathlib import Path

import pytest
import z3

from freqhorn_bnd import BoundedExplorer, ExplorationStatus, parse_chc_file
from freqhorn_bnd.vc import build_verification_condition

ROOT = Path(__file__).resolve().parents[1]
EXAMPLES = ROOT / "examples"


def test_fixedpoint_rule_syntax_is_supported() -> None:
    program = parse_chc_file(EXAMPLES / "rule_syntax.smt2")
    assert len(program.rules) == 3
    assert sum(rule.is_fact for rule in program.rules) == 1
    assert sum(rule.is_inductive for rule in program.rules) == 1
    assert sum(rule.is_query for rule in program.rules) == 1

    result = BoundedExplorer(program, timeout_ms=5_000).explore(upto=8)
    assert result.status is ExplorationStatus.COUNTEREXAMPLE
    assert result.explored_upto == 4


def test_pure_smtlib_forall_assertions_with_false_head_are_supported() -> None:
    program = parse_chc_file(EXAMPLES / "assert_syntax.smt2")
    assert len(program.rules) == 3
    assert any(
        str(rule.dst_relation.name()).startswith("__chc_bnd_assertion_error")
        for rule in program.rules
    )

    result = BoundedExplorer(program, timeout_ms=5_000).explore(upto=8)
    assert result.status is ExplorationStatus.COUNTEREXAMPLE
    assert result.explored_upto == 4


def test_pure_smtlib_interpreted_property_head_is_checked() -> None:
    program = parse_chc_file(EXAMPLES / "assert_property_head.smt2")
    result = BoundedExplorer(program, timeout_ms=5_000).explore(upto=8)
    assert result.status is ExplorationStatus.COUNTEREXAMPLE
    assert result.explored_upto == 4


def test_safe_acyclic_program_is_completely_unrolled(tmp_path: Path) -> None:
    source = tmp_path / "safe_acyclic.smt2"
    source.write_text(
        """
        (set-logic HORN)
        (declare-fun p (Int) Bool)
        (declare-fun q (Int) Bool)
        (assert (p 0))
        (assert (forall ((x Int)) (=> (p x) (q x))))
        (assert (forall ((x Int)) (=> (and (q x) (< x 0)) false)))
        (check-sat)
        """,
        encoding="utf-8",
    )
    program = parse_chc_file(source)
    assert program.maximum_acyclic_trace_length() == 3

    result = BoundedExplorer(program, timeout_ms=5_000).explore(upto=100)
    assert result.status is ExplorationStatus.COMPLETE_SAFE
    assert result.explored_upto == 3
    assert result.complete


def test_vc_uses_native_z3_arrays_and_retains_inner_quantifier(
    tmp_path: Path,
) -> None:
    source = tmp_path / "array_quantifier.smt2"
    source.write_text(
        """
        (set-logic HORN)
        (declare-var a (Array Int Int))
        (declare-var a1 (Array Int Int))
        (declare-var i Int)
        (declare-rel inv ((Array Int Int) Int))
        (declare-rel fail ())
        (rule (inv a 0))
        (rule
          (=> (and (inv a i)
                   (= a1 (store a i i)))
              (inv a1 (+ i 1))))
        (rule
          (=> (and (inv a i)
                   (forall ((k Int))
                     (=> (and (<= 0 k) (< k i))
                         (= (select a k) k)))
                   (> i 0))
              fail))
        (query fail)
        """,
        encoding="utf-8",
    )
    program = parse_chc_file(source, slice_program=False)
    trace = (
        next(rule for rule in program.rules if rule.is_fact),
        next(rule for rule in program.rules if rule.is_inductive),
        next(rule for rule in program.rules if rule.is_query),
    )
    vc = build_verification_condition(program, trace)
    assert isinstance(vc.formula, z3.BoolRef)
    assert any(z3.is_quantifier(node) for node in _walk(vc.formula))
    assert "select" in vc.formula.sexpr()
    assert "store" in vc.formula.sexpr()


def _walk(expr: z3.ExprRef):
    yield expr
    if z3.is_quantifier(expr):
        yield from _walk(expr.body())
    elif z3.is_app(expr):
        for child in expr.children():
            yield from _walk(child)


def test_clausal_or_horn_assertion_is_normalized(tmp_path: Path) -> None:
    source = tmp_path / "or_syntax.smt2"
    source.write_text(
        """
        (set-logic HORN)
        (declare-fun p (Int) Bool)
        (assert (p 0))
        (assert (forall ((x Int)) (or (not (p x)) (> x 0))))
        (check-sat)
        """,
        encoding="utf-8",
    )
    result = BoundedExplorer(parse_chc_file(source), timeout_ms=5_000).explore(upto=3)
    assert result.status is ExplorationStatus.COUNTEREXAMPLE
    assert result.explored_upto == 2


def test_nonlinear_chc_is_rejected(tmp_path: Path) -> None:
    source = tmp_path / "nonlinear.smt2"
    source.write_text(
        """
        (set-logic HORN)
        (declare-fun p (Int) Bool)
        (declare-fun q (Int) Bool)
        (declare-fun r (Int) Bool)
        (assert (p 0))
        (assert (q 0))
        (assert (forall ((x Int)) (=> (and (p x) (q x)) (r x))))
        (assert (forall ((x Int)) (=> (r x) false)))
        (check-sat)
        """,
        encoding="utf-8",
    )
    with pytest.raises(ValueError, match="nonlinear"):
        parse_chc_file(source, slice_program=False)


def test_trace_enumeration_does_not_use_python_recursion(tmp_path: Path) -> None:
    source = tmp_path / "deep.smt2"
    source.write_text(
        """
        (declare-var x Int)
        (declare-rel p (Int))
        (declare-rel fail ())
        (rule (p 0))
        (rule (=> (p x) (p x)))
        (rule (=> (p x) fail))
        (query fail)
        """,
        encoding="utf-8",
    )
    explorer = BoundedExplorer(parse_chc_file(source), timeout_ms=5_000)
    trace = next(explorer.traces_of_length(1_500))
    assert len(trace) == 1_500


def test_synthetic_error_relation_name_cannot_collide(tmp_path: Path) -> None:
    source = tmp_path / "collision.smt2"
    source.write_text(
        """
        (set-logic HORN)
        (declare-fun __chc_bnd_assertion_error () Bool)
        (declare-fun p (Int) Bool)
        (assert (p 0))
        (assert (forall ((x Int)) (=> (p x) (> x 0))))
        (check-sat)
        """,
        encoding="utf-8",
    )
    program = parse_chc_file(source, slice_program=False)
    query_names = {str(relation.name()) for relation in program.query_relations}
    assert "__chc_bnd_assertion_error_1" in query_names


def test_every_constructed_ssa_can_be_dumped_to_separate_files(
    tmp_path: Path,
) -> None:
    dump_dir = tmp_path / "ssa"
    program = parse_chc_file(EXAMPLES / "assert_syntax.smt2")
    explorer = BoundedExplorer(
        program,
        timeout_ms=5_000,
        ssa_dump_dir=dump_dir,
    )

    result = explorer.explore(upto=8)
    assert result.status is ExplorationStatus.COUNTEREXAMPLE

    files = sorted(dump_dir.glob("ssa_*.smt2"))
    assert explorer.ssa_dump_count == 3
    assert [path.name for path in files] == [
        "ssa_000001_depth_000002.smt2",
        "ssa_000002_depth_000003.smt2",
        "ssa_000003_depth_000004.smt2",
    ]

    for path in files:
        text = path.read_text(encoding="utf-8")
        assert "; trace-length:" in text
        assert "; rule-ids:" in text
        assert "; step 0:" in text
        assert text.count("(assert") == int(
            next(
                line.split(":", 1)[1]
                for line in text.splitlines()
                if line.startswith("; trace-length:")
            )
        )
        replay = z3.Solver()
        replay.from_string(text)
        assert replay.check() in (z3.sat, z3.unsat, z3.unknown)


def test_ssa_dump_directory_must_be_empty(tmp_path: Path) -> None:
    dump_dir = tmp_path / "ssa"
    dump_dir.mkdir()
    (dump_dir / "keep.txt").write_text("do not overwrite", encoding="utf-8")

    with pytest.raises(ValueError, match="must be empty"):
        BoundedExplorer(
            parse_chc_file(EXAMPLES / "assert_syntax.smt2"),
            ssa_dump_dir=dump_dir,
        )


def test_solver_pool_reuses_longest_common_prefix(tmp_path: Path) -> None:
    source = tmp_path / "branching.smt2"
    source.write_text(
        """
        (declare-var x Int)
        (declare-rel p (Int))
        (declare-rel q (Int))
        (declare-rel r (Int))
        (declare-rel fail ())
        (rule (p 0))
        (rule (=> (p x) (q x)))
        (rule (=> (q x) fail))
        (rule (=> (q x) (r x)))
        (rule (=> (r x) fail))
        (query fail)
        """,
        encoding="utf-8",
    )
    explorer = BoundedExplorer(parse_chc_file(source), timeout_ms=5_000)
    short_trace = next(explorer.traces_of_length(3))
    long_trace = next(explorer.traces_of_length(4))

    assert explorer.check_trace(short_trace).status.value == "sat"
    assert explorer.check_trace(long_trace).status.value == "sat"

    activity = explorer.solver_pool.last_check
    assert activity is not None
    assert not activity.created_context
    assert activity.common_prefix_length == 2
    assert activity.popped_steps == 1
    assert activity.pushed_steps == 2

    pool = explorer.solver_statistics
    assert pool.contexts == 1
    assert pool.solvers_created == 1
    assert pool.traces_reused == 1
    assert pool.common_prefix_steps_reused == 2
    assert pool.pushes == 5
    assert pool.pops == 1

    ssa = explorer.ssa_statistics
    assert ssa.cache_hits == 2
    assert ssa.cache_misses == 5


def test_solver_pool_keeps_only_the_sat_prefix_after_unsat(tmp_path: Path) -> None:
    source = tmp_path / "unsat_suffix.smt2"
    source.write_text(
        """
        (declare-var x Int)
        (declare-rel p (Int))
        (declare-rel q (Int))
        (declare-rel fail ())
        (rule (p 0))
        (rule (=> (p x) (q x)))
        (rule (=> (and (q x) (< x 0)) fail))
        (query fail)
        """,
        encoding="utf-8",
    )
    explorer = BoundedExplorer(parse_chc_file(source), timeout_ms=5_000)
    trace = next(explorer.traces_of_length(3))
    check = explorer.check_trace(trace)

    assert check.status.value == "unsat"
    assert check.unsat_prefix_length == 3
    assert explorer.solver_pool.context_prefixes == (
        tuple(rule.rule_id for rule in trace[:2]),
    )
    assert explorer.solver_statistics.pushes == 3
    assert explorer.solver_statistics.pops == 1


def test_fresh_solver_mode_disables_cross_trace_reuse(tmp_path: Path) -> None:
    source = tmp_path / "branching_fresh.smt2"
    source.write_text(
        """
        (declare-var x Int)
        (declare-rel p (Int))
        (declare-rel q (Int))
        (declare-rel r (Int))
        (declare-rel fail ())
        (rule (p 0))
        (rule (=> (p x) (q x)))
        (rule (=> (q x) fail))
        (rule (=> (q x) (r x)))
        (rule (=> (r x) fail))
        (query fail)
        """,
        encoding="utf-8",
    )
    explorer = BoundedExplorer(
        parse_chc_file(source), timeout_ms=5_000, use_solver_pool=False
    )
    assert explorer.check_trace(next(explorer.traces_of_length(3))).status.value == "sat"
    assert explorer.check_trace(next(explorer.traces_of_length(4))).status.value == "sat"

    pool = explorer.solver_statistics
    assert pool.contexts == 2
    assert pool.solvers_created == 2
    assert pool.traces_reused == 0


def test_pooled_and_fresh_solvers_agree_on_branching_trace_set(
    tmp_path: Path,
) -> None:
    source = tmp_path / "branching_equivalence.smt2"
    source.write_text(
        """
        (declare-var x Int)
        (declare-var y Int)
        (declare-rel p (Int))
        (declare-rel fail ())
        (rule (p 0))
        (rule (=> (and (p x) (= y (+ x 1))) (p y)))
        (rule (=> (and (p x) (= y (+ x 2))) (p y)))
        (rule (=> (and (p x) (= y (- x 1))) (p y)))
        (rule (=> (and (p x) (= x 3)) fail))
        (query fail)
        """,
        encoding="utf-8",
    )
    program = parse_chc_file(source)
    generator = BoundedExplorer(program)
    traces = [
        trace
        for depth in range(2, 7)
        for trace in generator.traces_of_length(depth)
    ]

    pooled = BoundedExplorer(program, timeout_ms=5_000)
    fresh = BoundedExplorer(
        program, timeout_ms=5_000, use_solver_pool=False
    )
    pooled_results = [
        (check.status, check.unsat_prefix_length)
        for trace in traces
        for check in [pooled.check_trace(trace)]
    ]
    fresh_results = [
        (check.status, check.unsat_prefix_length)
        for trace in traces
        for check in [fresh.check_trace(trace)]
    ]

    assert pooled_results == fresh_results
    assert pooled.solver_statistics.checks < fresh.solver_statistics.checks
