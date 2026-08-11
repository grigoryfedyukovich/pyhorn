from __future__ import annotations

import json
from pathlib import Path

import z3

from pyhorn_bnd import parse_chc_file
from pyhorn_bnd.cli import main
from pyhorn_bnd.houdini import HoudiniStatus, MultiHoudini, run_seed_houdini
from pyhorn_bnd.seedminer import SeedMiner

ROOT = Path(__file__).resolve().parents[1]
EXAMPLES = ROOT / "examples" / "seed_houdini"


def _relation(program, name: str) -> z3.FuncDeclRef:
    return next(relation for relation in program.relations if str(relation.name()) == name)


def _equivalent(left: z3.BoolRef, right: z3.BoolRef) -> bool:
    solver = z3.Solver()
    solver.add(z3.Xor(left, right))
    return solver.check() == z3.unsat


def test_seedminer_projects_query_tree_and_fact_arguments() -> None:
    program = parse_chc_file(EXAMPLES / "counter_safe.smt2", slice_program=False)
    result = SeedMiner(program).mine()
    inv = _relation(program, "inv")
    variable = result.variables[inv][0]

    assert any(_equivalent(candidate, variable <= 10) for candidate in result.candidates[inv])
    assert any(_equivalent(candidate, variable == 0) for candidate in result.candidates[inv])
    assert any(
        observation.role == "source:query-negation"
        and observation.relation == inv
        and _equivalent(observation.candidate, variable <= 10)
        for observation in result.observations
    )
    assert result.statistics.rules_examined == 3
    assert result.statistics.boolean_nodes_seen > 0


def test_seedminer_mine_is_idempotent() -> None:
    program = parse_chc_file(EXAMPLES / "counter_safe.smt2", slice_program=False)
    miner = SeedMiner(program)

    first = miner.mine()
    second = miner.mine()

    assert first.statistics == second.statistics
    assert [item.candidate.sexpr() for item in first.observations] == [
        item.candidate.sexpr() for item in second.observations
    ]
    assert {
        str(relation.name()): [candidate.sexpr() for candidate in candidates]
        for relation, candidates in first.candidates.items()
    } == {
        str(relation.name()): [candidate.sexpr() for candidate in candidates]
        for relation, candidates in second.candidates.items()
    }


def test_seedminer_collects_array_select_candidate(tmp_path: Path) -> None:
    source = tmp_path / "array_seed.smt2"
    source.write_text(
        """
        (declare-var a (Array Int Int))
        (declare-var i Int)
        (declare-rel inv ((Array Int Int) Int))
        (declare-rel fail ())
        (rule (inv a 0))
        (rule (=> (and (inv a i) (< (select a 0) 0)) fail))
        (query fail)
        """,
        encoding="utf-8",
    )
    program = parse_chc_file(source, slice_program=False)
    seeds = SeedMiner(program).mine()
    inv = _relation(program, "inv")

    assert any("select" in candidate.sexpr() for candidate in seeds.candidates[inv])


def test_multihoudini_removes_all_candidates_falsified_by_countermodels() -> None:
    program = parse_chc_file(EXAMPLES / "counter_safe.smt2", slice_program=False)
    seeds = SeedMiner(program).mine()
    inv = _relation(program, "inv")
    variable = seeds.variables[inv][0]
    candidates = {inv: {variable >= 0, variable <= 10, variable == 0}}

    result = MultiHoudini(program, seeds.variables, timeout_ms=5_000).run(candidates)

    assert result.status is HoudiniStatus.SUCCESS
    assert result.statistics.candidates_initial == 3
    assert result.statistics.candidates_removed == 1
    assert result.statistics.candidates_remaining == 2
    retained = result.candidates[inv]
    assert any(_equivalent(candidate, variable >= 0) for candidate in retained)
    assert any(_equivalent(candidate, variable <= 10) for candidate in retained)
    assert not any(_equivalent(candidate, variable == 0) for candidate in retained)


def test_seedmined_candidates_prove_safe_counter() -> None:
    program = parse_chc_file(EXAMPLES / "counter_safe.smt2", slice_program=False)
    result = run_seed_houdini(program, timeout_ms=5_000)

    assert result.status is HoudiniStatus.SUCCESS
    assert not result.failures
    assert result.statistics.candidates_removed > 0
    assert result.statistics.candidates_remaining > 0


def test_multihoudini_handles_multiple_predicates() -> None:
    program = parse_chc_file(
        EXAMPLES / "multiple_predicates.smt2", slice_program=False
    )
    result = run_seed_houdini(program, timeout_ms=5_000)

    assert result.status is HoudiniStatus.SUCCESS
    assert {str(relation.name()) for relation in result.candidates} == {"p", "q"}
    assert result.statistics.solver_contexts == 3
    assert result.statistics.certification_checks == 4


def test_seed_houdini_reports_unknown_when_query_remains_reachable() -> None:
    program = parse_chc_file(EXAMPLES / "counter_unsafe.smt2", slice_program=False)
    result = run_seed_houdini(program, timeout_ms=5_000)

    assert result.status is HoudiniStatus.UNKNOWN
    assert result.failures
    assert any("not valid" in failure.reason for failure in result.failures)


def test_seed_houdini_cli_reports_only_success_or_unknown(capsys) -> None:
    assert main(["--seed-houdini", str(EXAMPLES / "counter_safe.smt2")]) == 0
    assert capsys.readouterr().out.strip() == "Success"

    assert main(["--seed-houdini", str(EXAMPLES / "counter_unsafe.smt2")]) == 2
    assert capsys.readouterr().out.strip() == "unknown"


def test_seed_houdini_json_reports_fresh_certification(capsys) -> None:
    path = EXAMPLES / "counter_safe.smt2"
    assert main(["--seed-houdini", "--json", str(path)]) == 0
    payload = json.loads(capsys.readouterr().out)

    assert payload["status"] == "success"
    assert payload["houdini"]["certification_checks"] == 3
