from __future__ import annotations

from pathlib import Path

import z3

from pyhorn_bnd import (
    BndExplSmtDumpBuilder,
    BoundedExplorer,
    ExplorationStatus,
    HoudiniStatus,
    SeedMiner,
    VerificationConditionBuilder,
    parse_chc_file,
    run_seed_houdini,
)

ROOT = Path(__file__).resolve().parents[1]
EXAMPLES = ROOT / "examples" / "real_arithmetic"


def _relation(program, name: str) -> z3.FuncDeclRef:
    return next(
        relation for relation in program.relations if str(relation.name()) == name
    )


def _equivalent(left: z3.BoolRef, right: z3.BoolRef) -> bool:
    solver = z3.Solver()
    solver.add(z3.Xor(left, right))
    return solver.check() == z3.unsat


def _walk(expression: z3.ExprRef):
    yield expression
    if z3.is_quantifier(expression):
        yield from _walk(expression.body())
    elif z3.is_app(expression):
        for child in expression.children():
            yield from _walk(child)


def test_real_sort_profile_and_exact_rationals_are_preserved() -> None:
    program = parse_chc_file(
        EXAMPLES / "fixedpoint_safe.smt2", slice_program=False
    )
    inv = _relation(program, "inv")

    assert program.arithmetic_sorts.uses_real
    assert not program.arithmetic_sorts.uses_integer
    assert not program.arithmetic_sorts.is_mixed
    assert inv.domain(0).kind() == z3.Z3_REAL_SORT

    transition = next(rule for rule in program.rules if rule.is_inductive)
    quarter = z3.simplify(transition.dst_args[0].arg(1))
    assert z3.is_rational_value(quarter)
    assert quarter.numerator_as_long() == 1
    assert quarter.denominator_as_long() == 4


def test_seed_houdini_proves_linear_real_invariant() -> None:
    program = parse_chc_file(
        EXAMPLES / "fixedpoint_safe.smt2", slice_program=False
    )
    result = run_seed_houdini(program, timeout_ms=5_000, random_seed=1)
    inv = _relation(program, "inv")
    variable = result.variables[inv][0]

    assert result.status is HoudiniStatus.SUCCESS
    assert variable.sort().kind() == z3.Z3_REAL_SORT
    assert any(
        _equivalent(candidate, variable <= z3.RealVal(1))
        for candidate in result.candidates[inv]
    )


def test_bounded_explorer_finds_real_counterexample_in_both_solver_modes() -> None:
    program = parse_chc_file(EXAMPLES / "fixedpoint_unsafe.smt2")

    for solver_mode in ("pool", "fresh"):
        result = BoundedExplorer(
            program,
            timeout_ms=5_000,
            solver_mode=solver_mode,
        ).explore(upto=8)
        assert result.status is ExplorationStatus.COUNTEREXAMPLE
        assert result.explored_upto == 6


def test_pure_smtlib_real_assertions_are_supported() -> None:
    program = parse_chc_file(EXAMPLES / "assert_unsafe.smt2")
    assert program.arithmetic_sorts.uses_real
    assert not program.arithmetic_sorts.uses_integer

    result = BoundedExplorer(program, timeout_ms=5_000).explore(upto=8)
    assert result.status is ExplorationStatus.COUNTEREXAMPLE
    assert result.explored_upto == 5


def test_mixed_integer_real_reasoning_uses_to_real() -> None:
    program = parse_chc_file(
        EXAMPLES / "mixed_int_real_safe.smt2", slice_program=False
    )
    result = run_seed_houdini(program, timeout_ms=5_000, random_seed=1)
    inv = _relation(program, "inv")
    integer_variable, real_variable = result.variables[inv]

    assert program.arithmetic_sorts.is_mixed
    assert integer_variable.sort().kind() == z3.Z3_INT_SORT
    assert real_variable.sort().kind() == z3.Z3_REAL_SORT
    assert result.status is HoudiniStatus.SUCCESS
    assert any(
        _equivalent(candidate, real_variable <= z3.ToReal(integer_variable))
        for candidate in result.candidates[inv]
    )


def test_real_valued_array_and_quantified_candidate_are_supported() -> None:
    program = parse_chc_file(
        EXAMPLES / "array_real_safe.smt2", slice_program=False
    )
    seeds = SeedMiner(program).mine()
    result = run_seed_houdini(program, timeout_ms=5_000, random_seed=1)
    inv = _relation(program, "inv")

    assert program.arithmetic_sorts.is_mixed
    assert inv.domain(0).kind() == z3.Z3_ARRAY_SORT
    assert inv.domain(0).range().kind() == z3.Z3_REAL_SORT
    assert any(
        z3.is_quantifier(node)
        for candidate in seeds.candidates[inv]
        for node in _walk(candidate)
    )
    assert any(
        z3.is_select(node)
        for candidate in seeds.candidates[inv]
        for node in _walk(candidate)
    )
    assert result.status is HoudiniStatus.SUCCESS



def test_integer_state_can_contain_real_division_and_implicit_coercions() -> None:
    program = parse_chc_file(
        EXAMPLES / "integer_state_real_division_safe.smt2",
        slice_program=False,
    )
    inv = _relation(program, "inv")
    result = run_seed_houdini(program, timeout_ms=5_000, random_seed=1)

    assert all(
        inv.domain(index).kind() == z3.Z3_INT_SORT
        for index in range(inv.arity())
    )
    assert program.arithmetic_sorts.is_mixed
    assert any(
        "to_real" in node.sexpr()
        for rule in program.rules
        for node in _walk(rule.body)
    )
    assert result.status is HoudiniStatus.SUCCESS

def test_nonlinear_real_trace_is_left_to_z3() -> None:
    program = parse_chc_file(EXAMPLES / "nonlinear_unsafe.smt2")
    result = BoundedExplorer(program, timeout_ms=5_000).explore(upto=4)

    assert result.status is ExplorationStatus.COUNTEREXAMPLE
    assert result.explored_upto == 3
    assert result.trace_check is not None
    assert "*" in result.trace_check.vc.formula.sexpr()


def test_real_ssa_and_bnd_dump_preserve_real_declarations() -> None:
    program = parse_chc_file(EXAMPLES / "fixedpoint_unsafe.smt2")
    trace = next(BoundedExplorer(program).traces_of_length(6))
    vc = VerificationConditionBuilder(program).build(trace)

    state_variables = [
        variable
        for step in vc.steps
        for state in (step.source_state, step.destination_state)
        if state is not None
        for variable in state.variables
    ]
    assert state_variables
    assert all(variable.sort().kind() == z3.Z3_REAL_SORT for variable in state_variables)

    smt2 = BndExplSmtDumpBuilder(program).to_smt2(
        trace,
        bound=6,
        result="sat",
    )
    assert "() Real" in smt2
    assert "() Int" not in smt2
    replay = z3.Solver()
    replay.from_string(smt2)
    assert replay.check() == z3.sat
