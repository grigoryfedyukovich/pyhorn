from __future__ import annotations

from pathlib import Path

import pytest
import z3

from pyhorn_bnd import BoundedExplorer, ExplorationStatus, parse_chc_file
from pyhorn_bnd.vc import build_verification_condition

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


def test_every_checked_trace_is_dumped_in_bnd_expl_format(
    tmp_path: Path,
) -> None:
    dump_dir = tmp_path / "unrollings"
    program = parse_chc_file(EXAMPLES / "assert_syntax.smt2")
    explorer = BoundedExplorer(
        program,
        timeout_ms=5_000,
        smt_dump_dir=dump_dir,
    )

    result = explorer.explore(upto=8)
    assert result.status is ExplorationStatus.COUNTEREXAMPLE

    files = sorted(dump_dir.glob("*.smt2"))
    assert explorer.smt_dump_count == 3
    assert [path.name for path in files] == [
        "assert_syntax_k2_unsat.smt2",
        "assert_syntax_k3_unsat.smt2",
        "assert_syntax_k4_sat.smt2",
    ]

    for path in files:
        text = path.read_text(encoding="utf-8")
        result_name = path.stem.rsplit("_", 1)[1]
        bound = int(path.stem.split("_k", 1)[1].split("_", 1)[0])
        assert text.startswith("; bnd/expl SMT dump\n")
        assert f"; bound: {bound}\n" in text
        assert f"; result: {result_name}\n" in text
        assert text.count("(assert") == 1
        assert "__bnd_var_" in text
        assert "__state_" not in text
        assert "__rule_" not in text
        assert "__pyhorn_" not in text
        replay = z3.Solver()
        replay.from_string(text)
        expected = {"sat": z3.sat, "unsat": z3.unsat}[result_name]
        assert replay.check() == expected


def test_smt_dump_directory_may_already_exist(tmp_path: Path) -> None:
    dump_dir = tmp_path / "unrollings"
    dump_dir.mkdir()
    marker = dump_dir / "keep.txt"
    marker.write_text("keep", encoding="utf-8")

    explorer = BoundedExplorer(
        parse_chc_file(EXAMPLES / "assert_syntax.smt2"),
        smt_dump_dir=dump_dir,
    )
    explorer.explore(upto=2)

    assert marker.read_text(encoding="utf-8") == "keep"
    assert (dump_dir / "assert_syntax_k2_unsat.smt2").is_file()


def test_abdu_05_dump_matches_cpp_reference(tmp_path: Path) -> None:
    source = EXAMPLES / "bench_horn_multiple" / "abdu_05.smt2"
    reference_dir = ROOT / "tests" / "data" / "bnd_expl_dumps" / "abdu_05"
    dump_dir = tmp_path / "unrollings"

    explorer = BoundedExplorer(
        parse_chc_file(source),
        timeout_ms=5_000,
        smt_dump_dir=dump_dir,
    )
    result = explorer.explore(upto=10)

    assert result.status is ExplorationStatus.BOUNDED_SAFE
    generated = {path.name: path for path in dump_dir.glob("*.smt2")}
    reference = {path.name: path for path in reference_dir.glob("*.smt2")}
    assert generated.keys() == reference.keys()
    assert len(generated) == 36

    for name, generated_path in generated.items():
        generated_assertions = z3.parse_smt2_file(str(generated_path))
        reference_assertions = z3.parse_smt2_file(str(reference[name]))
        assert len(generated_assertions) == 1
        assert len(reference_assertions) == 1

        equivalence = z3.Solver()
        equivalence.add(
            z3.Xor(generated_assertions[0], reference_assertions[0])
        )
        assert equivalence.check() == z3.unsat, name


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
    assert explorer.solver_mode == "fresh"
    assert pool.contexts == 0
    assert pool.solvers_created == 2
    assert pool.traces_reused == 0
    assert pool.pushes == 0
    assert pool.pops == 0
    assert pool.checks == 7


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
        program, timeout_ms=5_000, solver_mode="fresh"
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
    assert fresh.solver_statistics.solvers_created == len(traces)
    assert fresh.solver_statistics.pushes == 0
    assert fresh.solver_statistics.pops == 0





def test_solver_pool_defaults_to_sixteen_contexts_and_reuses_objects() -> None:
    from types import SimpleNamespace

    import z3

    from pyhorn_bnd.solver_pool import IncrementalSolverPool

    pool = IncrementalSolverPool(timeout_ms=5_000)
    assert pool.max_contexts == 16

    # Force 20 context misses with mutually unrelated one-step rule IDs. Once
    # the pool reaches 16 contexts, LRU contexts must be reset rather than
    # replaced by newly allocated Z3 solver objects.
    for rule_id in range(20):
        vc = SimpleNamespace(
            rule_ids=(rule_id,),
            steps=(SimpleNamespace(constraint=z3.BoolVal(True)),),
        )
        assert pool.check(vc).result == z3.sat

    stats = pool.statistics
    assert stats.contexts == 16
    assert stats.solvers_created == 16
    assert stats.contexts_recycled == 4


def test_cli_defaults_to_sixteen_solvers() -> None:
    from pyhorn_bnd.cli import _parser

    args = _parser().parse_args(["input.smt2"])
    assert args.max_solvers == 16
