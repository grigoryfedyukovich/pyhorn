from __future__ import annotations

import pytest

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
EXAMPLES = ROOT / "examples" / "string_theory"


def _relation(program, name: str) -> z3.FuncDeclRef:
    return next(
        relation for relation in program.relations if str(relation.name()) == name
    )


def _walk(expression: z3.ExprRef):
    yield expression
    if z3.is_quantifier(expression):
        yield from _walk(expression.body())
    elif z3.is_app(expression):
        for child in expression.children():
            yield from _walk(child)


def _equivalent(left: z3.BoolRef, right: z3.BoolRef) -> bool:
    solver = z3.Solver()
    solver.add(z3.Xor(left, right))
    return solver.check() == z3.unsat


def test_fixedpoint_string_commands_parse_through_general_smt_frontend() -> None:
    program = parse_chc_file(
        EXAMPLES / "fixedpoint_safe.smt2",
        slice_program=False,
    )
    inv = _relation(program, "inv")

    assert len(program.rules) == 3
    assert inv.domain(0).is_string()
    assert program.string_sorts.uses_string
    assert not program.string_sorts.uses_regular_expressions
    expressions = [
        expression
        for rule in program.rules
        for expression in (rule.body, *rule.src_args, *rule.dst_args)
    ]
    assert any(
        node.decl().kind() == z3.Z3_OP_SEQ_CONCAT
        for expression in expressions
        for node in _walk(expression)
        if z3.is_app(node)
    )


def test_seed_houdini_proves_string_contains_invariant() -> None:
    program = parse_chc_file(
        EXAMPLES / "fixedpoint_safe.smt2",
        slice_program=False,
    )
    result = run_seed_houdini(program, timeout_ms=5_000, random_seed=1)
    inv = _relation(program, "inv")
    variable = result.variables[inv][0]

    assert result.status is HoudiniStatus.SUCCESS
    assert variable.sort().is_string()
    assert any(
        _equivalent(candidate, z3.Not(z3.Contains(variable, z3.StringVal("b"))))
        for candidate in result.candidates[inv]
    )


def test_bounded_explorer_finds_string_counterexample_in_both_modes() -> None:
    program = parse_chc_file(EXAMPLES / "fixedpoint_unsafe.smt2")

    for solver_mode in ("pool", "fresh"):
        result = BoundedExplorer(
            program,
            timeout_ms=5_000,
            solver_mode=solver_mode,
        ).explore(upto=7)
        assert result.status is ExplorationStatus.COUNTEREXAMPLE
        assert result.explored_upto == 5


def test_pure_assert_string_chcs_are_supported() -> None:
    program = parse_chc_file(EXAMPLES / "assert_unsafe.smt2")
    result = BoundedExplorer(program, timeout_ms=5_000).explore(upto=6)

    assert program.string_sorts.uses_string
    assert result.status is ExplorationStatus.COUNTEREXAMPLE
    assert result.explored_upto == 4


def test_regex_candidates_are_preserved_and_certified() -> None:
    program = parse_chc_file(
        EXAMPLES / "regex_safe.smt2",
        slice_program=False,
    )
    seeds = SeedMiner(program).mine()
    result = run_seed_houdini(program, timeout_ms=5_000, random_seed=1)
    inv = _relation(program, "inv")

    assert program.string_sorts.uses_string
    assert program.string_sorts.uses_regular_expressions
    assert any(
        z3.is_app(node) and node.decl().kind() == z3.Z3_OP_SEQ_IN_RE
        for candidate in seeds.candidates[inv]
        for node in _walk(candidate)
    )
    assert result.status is HoudiniStatus.SUCCESS


def test_mixed_string_integer_length_invariant_is_supported() -> None:
    program = parse_chc_file(
        EXAMPLES / "mixed_string_int_safe.smt2",
        slice_program=False,
    )
    result = run_seed_houdini(program, timeout_ms=5_000, random_seed=1)
    inv = _relation(program, "inv")
    string_variable, integer_variable = result.variables[inv]

    assert program.string_sorts.uses_string
    assert program.arithmetic_sorts.uses_integer
    assert result.status is HoudiniStatus.SUCCESS
    assert any(
        _equivalent(candidate, z3.Length(string_variable) == integer_variable)
        for candidate in result.candidates[inv]
    )


def test_string_arrays_preserve_sorts_in_ssa_and_dump() -> None:
    program = parse_chc_file(
        EXAMPLES / "string_array_safe.smt2",
        slice_program=False,
    )
    result = run_seed_houdini(program, timeout_ms=5_000, random_seed=1)
    inv = _relation(program, "inv")

    assert inv.domain(0).kind() == z3.Z3_ARRAY_SORT
    assert inv.domain(0).range().is_string()
    assert result.status is HoudiniStatus.SUCCESS

    # Build a concrete fact/transition/query trace of length three.
    sliced = program.slice_to_queries()
    full_trace = next(BoundedExplorer(sliced).traces_of_length(3))
    vc = VerificationConditionBuilder(sliced).build(full_trace)
    state_variables = [
        variable
        for step in vc.steps
        for state in (step.source_state, step.destination_state)
        if state is not None
        for variable in state.variables
    ]
    assert any(
        variable.sort().kind() == z3.Z3_ARRAY_SORT
        and variable.sort().range().is_string()
        for variable in state_variables
    )

    smt2 = BndExplSmtDumpBuilder(sliced).to_smt2(
        full_trace,
        bound=3,
        result="unsat",
    )
    assert "(Array Int String)" in smt2
    replay = z3.Solver()
    replay.from_string(smt2)
    assert replay.check() == z3.unsat


def test_representative_string_operators_parse_and_solve() -> None:
    program = parse_chc_file(EXAMPLES / "operators_safe.smt2")
    result = BoundedExplorer(program, timeout_ms=5_000).explore(upto=3)
    sexprs = "\n".join(rule.body.sexpr() for rule in program.rules)

    for operator in (
        "str.len",
        "str.prefixof",
        "str.suffixof",
        "str.contains",
        "str.at",
        "str.substr",
        "str.indexof",
        "str.replace",
        "str.to_int",
        "str.from_int",
    ):
        assert operator in sexprs
    assert result.status is ExplorationStatus.COMPLETE_SAFE


def test_unicode_and_doubled_quote_literals_survive_command_translation() -> None:
    program = parse_chc_file(EXAMPLES / "unicode_safe.smt2", slice_program=False)
    inv = _relation(program, "inv")
    fact = next(rule for rule in program.rules if rule.is_fact)

    assert inv.domain(0).is_string()
    assert fact.dst_args[0].eq(z3.StringVal('λ"x'))


def test_fixedpoint_only_options_do_not_break_string_translation(
    tmp_path: Path,
) -> None:
    source = tmp_path / "fixedpoint_option_string.smt2"
    source.write_text(
        """
(set-logic HORN)
(set-option :fixedpoint.engine spacer)
(declare-rel inv (String))
(declare-rel fail ())
(rule (inv "ok"))
(rule (=> (and (inv "ok") false) fail))
(query fail)
""".strip()
        + "\n",
        encoding="utf-8",
    )

    program = parse_chc_file(source, slice_program=False)
    assert len(program.rules) == 2
    assert program.string_sorts.uses_string


@pytest.mark.parametrize(
    "filename",
    [
        "concat_prefix_safe.smt2",
        "regex_union_range_safe.smt2",
        "str_to_int_roundtrip_safe.smt2",
        "empty_suffix_safe.smt2",
        "fixedpoint_regex_safe.smt2",
    ],
)
def test_extended_string_theory_suite_is_safe(filename: str) -> None:
    program = parse_chc_file(EXAMPLES / filename, slice_program=False)
    assert program.string_sorts.uses_string
    result = run_seed_houdini(program, timeout_ms=5_000, random_seed=1)
    assert result.status is HoudiniStatus.SUCCESS


def test_regex_union_range_marks_regular_expression_profile() -> None:
    program = parse_chc_file(
        EXAMPLES / "regex_union_range_safe.smt2", slice_program=False
    )
    assert program.string_sorts.uses_string
    assert program.string_sorts.uses_regular_expressions


def test_disequality_unsafe_is_found_by_bounded_exploration() -> None:
    program = parse_chc_file(EXAMPLES / "disequality_unsafe.smt2")
    for solver_mode in ("pool", "fresh"):
        result = BoundedExplorer(
            program, timeout_ms=5_000, solver_mode=solver_mode
        ).explore(upto=6)
        assert result.status is ExplorationStatus.COUNTEREXAMPLE
        assert result.explored_upto == 3


def test_fixedpoint_regex_safe_uses_general_smt_frontend() -> None:
    program = parse_chc_file(
        EXAMPLES / "fixedpoint_regex_safe.smt2", slice_program=False
    )
    assert program.string_sorts.uses_string
    assert program.string_sorts.uses_regular_expressions
    result = run_seed_houdini(program, timeout_ms=5_000, random_seed=1)
    assert result.status is HoudiniStatus.SUCCESS
