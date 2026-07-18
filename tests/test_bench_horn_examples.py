from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path

import pytest
import z3

from pyhorn_bnd import parse_chc_file
from pyhorn_bnd.horn import HornProgram

ROOT = Path(__file__).resolve().parents[1]
EXAMPLES = ROOT / "examples" / "bench_horn"


@dataclass(frozen=True)
class ExampleExpectation:
    filename: str
    relation_signature: tuple[str, ...]
    required_operator_kinds: frozenset[int]
    required_source_tokens: tuple[str, ...] = ()
    forbidden_normalized_symbols: tuple[str, ...] = ()


CASES = (
    ExampleExpectation(
        "01_int_linear.smt2",
        ("Int", "Int"),
        frozenset({z3.Z3_OP_EQ, z3.Z3_OP_NOT}),
    ),
    ExampleExpectation(
        "02_bool_state.smt2",
        ("Bool",),
        frozenset({z3.Z3_OP_FALSE}),
    ),
    ExampleExpectation(
        "03_mixed_bool_int_mod_ite.smt2",
        ("Int", "Int", "Int", "Bool"),
        frozenset({z3.Z3_OP_ITE, z3.Z3_OP_MOD}),
    ),
    ExampleExpectation(
        "04_array_store_select.smt2",
        ("(Array Int Int)",),
        frozenset({z3.Z3_OP_STORE, z3.Z3_OP_SELECT}),
    ),
    ExampleExpectation(
        "05_const_array_and_ite.smt2",
        ("(Array Int Int)", "(Array Int Int)", "Int", "Int"),
        frozenset(
            {
                z3.Z3_OP_CONST_ARRAY,
                z3.Z3_OP_ITE,
                z3.Z3_OP_STORE,
                z3.Z3_OP_SELECT,
            }
        ),
        required_source_tokens=("(as const (Array Int Int))",),
    ),
    ExampleExpectation(
        "06_integer_div_mod.smt2",
        ("Int", "Int"),
        frozenset({z3.Z3_OP_IDIV, z3.Z3_OP_MOD}),
    ),
    ExampleExpectation(
        "07_nonlinear_multiplication.smt2",
        ("Int", "Int"),
        frozenset({z3.Z3_OP_MUL}),
    ),
    ExampleExpectation(
        "08_define_fun_or_ite.smt2",
        ("Int", "Int", "Int"),
        frozenset({z3.Z3_OP_OR, z3.Z3_OP_ITE}),
        required_source_tokens=("(define-fun tmp",),
        forbidden_normalized_symbols=("tmp",),
    ),
    ExampleExpectation(
        "09_distinct_and_ite.smt2",
        ("Int", "Int", "Int"),
        frozenset({z3.Z3_OP_NOT, z3.Z3_OP_EQ, z3.Z3_OP_ITE}),
        required_source_tokens=("(distinct",),
        forbidden_normalized_symbols=("distinct",),
    ),
    ExampleExpectation(
        "10_real_division_coercion.smt2",
        ("Int", "Int", "Int"),
        frozenset({z3.Z3_OP_DIV, z3.Z3_OP_TO_REAL}),
        required_source_tokens=("(/ a b)",),
    ),
)


def _walk(expr: z3.ExprRef):
    yield expr
    if z3.is_quantifier(expr):
        yield from _walk(expr.body())
    elif z3.is_app(expr):
        for child in expr.children():
            yield from _walk(child)


def _all_rule_expressions(program: HornProgram):
    for rule in program.rules:
        yield rule.body
        yield from rule.src_args
        yield from rule.dst_args


def _operator_kinds(program: HornProgram) -> set[int]:
    return {
        node.decl().kind()
        for expression in _all_rule_expressions(program)
        for node in _walk(expression)
        if z3.is_app(node)
    }


def _normalized_text(program: HornProgram) -> str:
    return "\n".join(
        expression.sexpr() for expression in _all_rule_expressions(program)
    )


def _assert_relation_arguments_are_well_typed(program: HornProgram) -> None:
    for rule in program.rules:
        if rule.src_relation is None:
            assert rule.src_args == ()
        else:
            assert len(rule.src_args) == rule.src_relation.arity()
            for index, argument in enumerate(rule.src_args):
                assert argument.sort().eq(rule.src_relation.domain(index))

        assert len(rule.dst_args) == rule.dst_relation.arity()
        for index, argument in enumerate(rule.dst_args):
            assert argument.sort().eq(rule.dst_relation.domain(index))


@pytest.mark.parametrize("case", CASES, ids=lambda case: case.filename)
def test_representative_bench_horn_case_is_parsed_and_normalized(
    case: ExampleExpectation,
) -> None:
    path = EXAMPLES / case.filename
    source = path.read_text(encoding="utf-8")
    program = parse_chc_file(path, slice_program=False)

    assert len(program.rules) == 3
    assert sum(rule.is_fact for rule in program.rules) == 1
    assert sum(rule.is_inductive for rule in program.rules) == 1
    assert sum(rule.is_query for rule in program.rules) == 1
    assert all(relation.arity() == 0 for relation in program.query_relations)

    state_relations = program.relations - program.query_relations
    assert len(state_relations) == 1
    state_relation = next(iter(state_relations))
    assert tuple(
        state_relation.domain(index).sexpr()
        for index in range(state_relation.arity())
    ) == case.relation_signature

    _assert_relation_arguments_are_well_typed(program)
    assert case.required_operator_kinds <= _operator_kinds(program)

    for token in case.required_source_tokens:
        assert token in source

    normalized = _normalized_text(program)
    for symbol in case.forbidden_normalized_symbols:
        assert symbol not in normalized


def test_every_extracted_smt2_file_has_an_explicit_expectation() -> None:
    actual = {path.name for path in EXAMPLES.glob("*.smt2")}
    expected = {case.filename for case in CASES}
    assert actual == expected
