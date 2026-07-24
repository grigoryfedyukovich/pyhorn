from __future__ import annotations

from pathlib import Path

import pytest
import z3

from pyhorn_bnd import HornParseError, SeedMiner, parse_chc_file, run_seed_houdini
from pyhorn_bnd.houdini import HoudiniStatus


ROOT = Path(__file__).resolve().parents[1]
EXAMPLES = ROOT / "examples" / "freqhorn_corner_cases"


def _relation(program, name: str) -> z3.FuncDeclRef:
    return next(relation for relation in program.relations if str(relation.name()) == name)


def _equivalent(left: z3.BoolRef, right: z3.BoolRef) -> bool:
    solver = z3.Solver()
    solver.add(z3.Xor(left, right))
    return solver.check() == z3.unsat


def test_infers_unique_terminal_nullary_query() -> None:
    program = parse_chc_file(
        EXAMPLES / "missing_explicit_query.smt2", slice_program=False
    )

    assert {str(relation.name()) for relation in program.query_relations} == {"fail"}
    assert len(program.rules) == 5
    assert sum(rule.is_query for rule in program.rules) == 1
    assert run_seed_houdini(program, timeout_ms=5_000, random_seed=1).success


def test_rejects_ambiguous_implicit_query(tmp_path: Path) -> None:
    source = tmp_path / "ambiguous_query.smt2"
    source.write_text(
        """
        (declare-rel p (Int))
        (declare-rel bad1 ())
        (declare-rel bad2 ())
        (declare-var x Int)
        (rule (p 0))
        (rule (=> (p x) bad1))
        (rule (=> (p x) bad2))
        """,
        encoding="utf-8",
    )

    with pytest.raises(HornParseError, match="multiple terminal nullary relations"):
        parse_chc_file(source, slice_program=False)


def test_numeric_equalities_mine_inductive_one_sided_bounds() -> None:
    program = parse_chc_file(
        EXAMPLES / "numeric_equality_bounds.smt2", slice_program=False
    )
    seeds = SeedMiner(program).mine()
    itp = _relation(program, "itp")
    left, right = seeds.variables[itp]

    assert any(_equivalent(candidate, left >= 1) for candidate in seeds.candidates[itp])
    assert any(_equivalent(candidate, right >= 1) for candidate in seeds.candidates[itp])
    assert run_seed_houdini(program, timeout_ms=5_000, random_seed=1).success


def test_repeated_query_arguments_preserve_complete_bad_state_pattern() -> None:
    program = parse_chc_file(
        EXAMPLES / "repeated_query_arguments.smt2", slice_program=False
    )
    seeds = SeedMiner(program).mine()
    inv = _relation(program, "inv")
    left, right = seeds.variables[inv]
    expected = z3.Not(z3.And(right >= 2452, left == right))

    assert any(_equivalent(candidate, expected) for candidate in seeds.candidates[inv])
    assert run_seed_houdini(program, timeout_ms=5_000, random_seed=1).success


def test_query_local_array_index_is_universally_closed() -> None:
    program = parse_chc_file(
        EXAMPLES / "quantified_array_invariant.smt2", slice_program=False
    )
    seeds = SeedMiner(program).mine()
    inv = _relation(program, "inv")

    quantified = [
        candidate
        for candidate in seeds.candidates[inv]
        if z3.is_quantifier(candidate) and "select" in candidate.sexpr()
    ]
    assert quantified
    result = run_seed_houdini(program, timeout_ms=5_000, random_seed=1)
    assert result.status is HoudiniStatus.SUCCESS
    assert result.statistics.certification_checks == len(program.rules)


def test_partial_quantified_models_fall_back_without_internal_failure() -> None:
    program = parse_chc_file(
        EXAMPLES / "quantified_model_fallback.smt2", slice_program=False
    )
    result = run_seed_houdini(program, timeout_ms=5_000, random_seed=1)

    assert result.status is HoudiniStatus.UNKNOWN
    assert result.failures
    assert all(
        "no individually satisfiable candidate" not in failure.reason
        for failure in result.failures
    )
    assert result.statistics.solver_checks > result.statistics.solver_contexts


def test_unsafe_quantified_array_never_reports_success() -> None:
    program = parse_chc_file(
        EXAMPLES / "unsafe_quantified_array.smt2", slice_program=False
    )
    result = run_seed_houdini(program, timeout_ms=5_000, random_seed=1)

    assert result.status is HoudiniStatus.UNKNOWN
    assert not result.success
