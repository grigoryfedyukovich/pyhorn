from __future__ import annotations

import json
from pathlib import Path

import pytest
import z3

from pyhorn_bnd import (
    BoundedExplorer,
    ExplorationStatus,
    HoudiniStatus,
    SeedMiner,
    parse_chc_file,
    run_seed_houdini,
)


ROOT = Path(__file__).resolve().parents[1]
EXAMPLES = ROOT / "examples" / "string_invariant_literature"
MANIFEST = json.loads((EXAMPLES / "manifest.json").read_text(encoding="utf-8"))
CASES = {item["file"]: item for item in MANIFEST["benchmarks"]}


def _walk(expression: z3.ExprRef):
    yield expression
    if z3.is_quantifier(expression):
        yield from _walk(expression.body())
    elif z3.is_app(expression):
        for child in expression.children():
            yield from _walk(child)


@pytest.mark.parametrize("filename", sorted(CASES))
def test_literature_string_benchmarks_parse_and_typecheck(filename: str) -> None:
    program = parse_chc_file(EXAMPLES / filename, slice_program=False)

    assert program.rules
    assert program.string_sorts.uses_string
    assert len(program.query_relations) == 1
    for rule in program.rules:
        if rule.src_relation is not None:
            assert len(rule.src_args) == rule.src_relation.arity()
            for index, argument in enumerate(rule.src_args):
                assert argument.sort().eq(rule.src_relation.domain(index))
        assert len(rule.dst_args) == rule.dst_relation.arity()
        for index, argument in enumerate(rule.dst_args):
            assert argument.sort().eq(rule.dst_relation.domain(index))


def test_hornstr_examples_contain_word_equations_and_regex_constraints() -> None:
    token = parse_chc_file(
        EXAMPLES / "hornstr_token_pass_safe.smt2",
        slice_program=False,
    )
    mu = parse_chc_file(
        EXAMPLES / "hornstr_mu_puzzle_safe.smt2",
        slice_program=False,
    )

    token_nodes = [
        node
        for rule in token.rules
        for expression in (rule.body, *rule.src_args, *rule.dst_args)
        for node in _walk(expression)
        if z3.is_app(node)
    ]
    mu_nodes = [
        node
        for rule in mu.rules
        for expression in (rule.body, *rule.src_args, *rule.dst_args)
        for node in _walk(expression)
        if z3.is_app(node)
    ]

    assert any(node.decl().kind() == z3.Z3_OP_SEQ_IN_RE for node in token_nodes)
    assert any(node.decl().kind() == z3.Z3_OP_RE_STAR for node in token_nodes)
    assert any(node.decl().kind() == z3.Z3_OP_SEQ_CONCAT for node in token_nodes)
    assert any(node.decl().kind() == z3.Z3_OP_SEQ_CONCAT for node in mu_nodes)
    assert sum(rule.is_inductive for rule in mu.rules) == 4


def test_regex_complement_is_accepted_and_seed_houdini_can_prove_closure() -> None:
    program = parse_chc_file(
        EXAMPLES / "regex_alphabet_closure_safe.smt2",
        slice_program=False,
    )
    expressions = [rule.body for rule in program.rules]

    assert any(
        node.decl().kind() == z3.Z3_OP_RE_COMPLEMENT
        for expression in expressions
        for node in _walk(expression)
        if z3.is_app(node)
    )
    result = run_seed_houdini(program, timeout_ms=5_000, random_seed=1)
    assert result.status is HoudiniStatus.SUCCESS


@pytest.mark.parametrize(
    "filename",
    [
        "copy_decomposition_safe.smt2",
        "html_escape_stream_safe.smt2",
        "replace_sanitize_safe.smt2",
        "prefix_closure_safe.smt2",
    ],
)
def test_local_string_program_invariants_are_solved_by_seed_houdini(
    filename: str,
) -> None:
    program = parse_chc_file(EXAMPLES / filename, slice_program=False)
    result = run_seed_houdini(program, timeout_ms=5_000, random_seed=1)

    assert result.status is HoudiniStatus.SUCCESS
    assert result.statistics.candidates_remaining >= 1
    assert result.statistics.certification_checks == len(program.rules)


@pytest.mark.parametrize(
    ("filename", "expected_depth"),
    [
        ("hornstr_mu_puzzle_unsafe_miu.smt2", 3),
        ("html_escape_stream_unsafe.smt2", 3),
        ("short_word_unsafe.smt2", 3),
    ],
)
def test_reachable_string_targets_are_found_in_both_solver_modes(
    filename: str,
    expected_depth: int,
) -> None:
    program = parse_chc_file(EXAMPLES / filename)

    for solver_mode in ("pool", "fresh"):
        result = BoundedExplorer(
            program,
            timeout_ms=5_000,
            solver_mode=solver_mode,
        ).explore(upto=5)
        assert result.status is ExplorationStatus.COUNTEREXAMPLE
        assert result.explored_upto == expected_depth


@pytest.mark.parametrize(
    "filename",
    ["hornstr_mu_puzzle_safe.smt2", "coffee_can_odd_white_safe.smt2"],
)
def test_syntactic_seedminer_does_not_overclaim_hard_regular_problems(
    filename: str,
) -> None:
    program = parse_chc_file(EXAMPLES / filename, slice_program=False)
    seeds = SeedMiner(program).mine()
    result = run_seed_houdini(program, timeout_ms=2_000, random_seed=1)

    assert seeds.candidate_count > 0
    assert result.status is HoudiniStatus.UNKNOWN
    assert result.failures
