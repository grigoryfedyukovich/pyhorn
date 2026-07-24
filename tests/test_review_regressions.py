from __future__ import annotations

import ast
from pathlib import Path

import z3

import pyhorn_bnd
from pyhorn_bnd import BoundedExplorer, parse_chc_file
from pyhorn_bnd.cli import _parser
from pyhorn_bnd.seedminer import _canonical_variables
from pyhorn_bnd.vc import _smt_symbol

ROOT = Path(__file__).resolve().parents[1]
EXAMPLES = ROOT / "examples"
SRC = ROOT / "src" / "pyhorn_bnd"


def test_runtime_package_exposes_version() -> None:
    assert pyhorn_bnd.__version__ == "0.0.11"


def test_source_package_contains_no_runtime_assert_statements() -> None:
    for path in SRC.glob("*.py"):
        tree = ast.parse(path.read_text(encoding="utf-8"), filename=str(path))
        assert not any(isinstance(node, ast.Assert) for node in ast.walk(tree)), path


def test_parser_uses_in_memory_source_not_fixedpoint_parse_file(monkeypatch) -> None:
    def forbidden_parse_file(*_args, **_kwargs):
        raise AssertionError("parse_file must not be called")

    monkeypatch.setattr(z3.Fixedpoint, "parse_file", forbidden_parse_file)
    program = parse_chc_file(EXAMPLES / "rule_syntax.smt2")
    assert len(program.rules) == 3


def test_canonical_variable_allocator_does_not_mutate_input_names() -> None:
    relation = z3.Function("p", z3.IntSort(), z3.BoolSort())
    used = {"p", "__inv_p_0"}
    original = set(used)

    variables, updated = _canonical_variables(relation, used)

    assert used == original
    assert str(variables[0]) == "__inv_p_0_1"
    assert "__inv_p_0_1" in updated


def test_exact_prefix_hit_reuses_cached_model_without_another_check() -> None:
    program = parse_chc_file(EXAMPLES / "assert_syntax.smt2")
    explorer = BoundedExplorer(program, timeout_ms=5_000)
    trace = next(explorer.traces_of_length(4))

    first = explorer.check_trace(trace)
    checks_after_first = explorer.solver_statistics.checks
    second = explorer.check_trace(trace)

    assert first.status.value == "sat"
    assert second.status.value == "sat"
    assert second.model is not None
    assert explorer.solver_statistics.checks == checks_after_first
    assert explorer.solver_statistics.exact_prefix_hits == 1


def test_ssa_cache_is_bounded_and_reports_evictions() -> None:
    program = parse_chc_file(EXAMPLES / "assert_syntax.smt2")
    explorer = BoundedExplorer(program, max_cached_ssa_steps=2)
    loop = next(rule for rule in program.rules if rule.is_inductive)

    for position in range(8):
        explorer.vc_builder.build_step(loop, position)

    stats = explorer.ssa_statistics
    assert stats.cached_steps <= 2
    assert stats.cached_states <= 2
    assert stats.cache_evictions > 0


def test_smt_symbol_quoting_avoids_z3_allocations_for_common_names() -> None:
    assert _smt_symbol("plain_name") == "plain_name"
    assert _smt_symbol("name with space") == "|name with space|"
    assert _smt_symbol("let") == "|let|"


def test_cli_exposes_bounded_ssa_cache_default() -> None:
    args = _parser().parse_args(["input.smt2"])
    assert args.max_ssa_cache_steps == 65_536
