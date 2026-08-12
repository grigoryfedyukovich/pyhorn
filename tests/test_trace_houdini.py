from __future__ import annotations

import json
import os
import subprocess
import sys
import time
from pathlib import Path

import pytest
import z3

from pyhorn_bnd import (
    CandidateMap,
    HoudiniStatus,
    SeedMiner,
    TraceCandidateMiner,
    mutate_candidates,
    parse_chc_file,
    run_seed_houdini,
    run_trace_houdini,
)
from pyhorn_bnd.cli import main

ROOT = Path(__file__).resolve().parents[1]
LENGTH_EXAMPLES = ROOT / "examples" / "string_length_literature"
TRACE_EXAMPLES = ROOT / "examples" / "trace_houdini"


def _relation(program, name: str) -> z3.FuncDeclRef:
    return next(
        relation for relation in program.relations if str(relation.name()) == name
    )


def _equivalent(left: z3.BoolRef, right: z3.BoolRef) -> bool:
    solver = z3.Solver()
    solver.add(z3.Xor(left, right))
    return solver.check() == z3.unsat


def test_trace_miner_extracts_reachable_prefix_models_and_parity() -> None:
    path = LENGTH_EXAMPLES / "append_two_parity_safe.smt2"
    program = parse_chc_file(path, slice_program=False)
    seeds = SeedMiner(program).mine()
    trace_result = TraceCandidateMiner(
        program,
        seeds.variables,
        max_depth=6,
        models_per_prefix=1,
        timeout_ms=5_000,
    ).mine()
    inv = _relation(program, "inv")
    string = seeds.variables[inv][0]

    assert trace_result.statistics.models_extracted >= 5
    assert {sample.depth for sample in trace_result.samples} >= {1, 2, 3, 4}
    assert any(
        _equivalent(candidate, z3.Length(string) % 2 == 0)
        for candidate in trace_result.candidates[inv]
    )


def test_trace_houdini_proves_modular_string_length_invariant() -> None:
    path = LENGTH_EXAMPLES / "append_two_parity_safe.smt2"
    program = parse_chc_file(path, slice_program=False)

    assert run_seed_houdini(program, timeout_ms=5_000).status is HoudiniStatus.UNKNOWN
    result = run_trace_houdini(
        program,
        trace_depth=6,
        models_per_prefix=1,
        timeout_ms=5_000,
    )

    assert result.status is HoudiniStatus.SUCCESS
    assert result.trace_result is not None
    assert result.trace_result.statistics.candidates_mined > 0
    inv = _relation(program, "inv")
    string = result.variables[inv][0]
    assert any(
        _equivalent(candidate, z3.Length(string) % 2 == 0)
        for candidate in result.candidates[inv]
    )


def test_trace_miner_finds_integer_affine_relation() -> None:
    program = parse_chc_file(
        TRACE_EXAMPLES / "integer_affine_safe.smt2", slice_program=False
    )
    seeds = SeedMiner(program).mine()
    trace_result = TraceCandidateMiner(
        program,
        seeds.variables,
        max_depth=6,
        models_per_prefix=1,
        timeout_ms=5_000,
    ).mine()
    inv = _relation(program, "inv")
    x, y = seeds.variables[inv]

    assert any(
        _equivalent(candidate, y == 2 * x)
        for candidate in trace_result.candidates[inv]
    )


def test_trace_sampler_diversifies_nondeterministic_prefix_models(
    tmp_path: Path,
) -> None:
    source = tmp_path / "nondeterministic_fact.smt2"
    source.write_text(
        """
        (declare-var x Int)
        (declare-rel inv (Int))
        (declare-rel fail ())
        (rule (inv x))
        (rule (=> (and (inv x) (not (= x x))) fail))
        (query fail)
        """,
        encoding="utf-8",
    )
    program = parse_chc_file(source, slice_program=False)
    seeds = SeedMiner(program).mine()
    trace_result = TraceCandidateMiner(
        program,
        seeds.variables,
        max_depth=1,
        models_per_prefix=3,
        timeout_ms=5_000,
    ).mine()

    values = {
        sample.values[0].sexpr()
        for sample in trace_result.samples
        if str(sample.relation.name()) == "inv"
    }
    assert len(values) == 3


def test_trace_candidates_remain_soundly_filtered_on_unsafe_input() -> None:
    program = parse_chc_file(
        LENGTH_EXAMPLES / "length_counter_desync_unsafe.smt2",
        slice_program=False,
    )
    result = run_trace_houdini(
        program,
        trace_depth=5,
        models_per_prefix=1,
        timeout_ms=5_000,
    )

    assert result.status is HoudiniStatus.UNKNOWN
    assert result.failures


def test_trace_houdini_cli_and_json(capsys) -> None:
    path = LENGTH_EXAMPLES / "append_two_parity_safe.smt2"
    assert (
        main(
            [
                "--trace-houdini",
                "--trace-depth",
                "6",
                "--trace-models-per-prefix",
                "1",
                str(path),
            ]
        )
        == 0
    )
    assert capsys.readouterr().out.strip() == "Success"

    assert (
        main(
            [
                "--trace-houdini",
                "--trace-depth",
                "6",
                "--trace-models-per-prefix",
                "1",
                "--json",
                str(path),
            ]
        )
        == 0
    )
    payload = json.loads(capsys.readouterr().out)
    assert payload["status"] == "success"
    assert payload["trace_mining"]["models_extracted"] >= 5
    assert payload["trace_mining"]["candidates"] > 0


def test_trace_houdini_improves_original_affine_and_modular_cases() -> None:
    for filename in (
        "abdu_02_affine_safe.smt2",
        "count_by_2_modular_safe.smt2",
    ):
        program = parse_chc_file(TRACE_EXAMPLES / filename, slice_program=False)
        seed = run_seed_houdini(program, timeout_ms=5_000, random_seed=1)
        trace = run_trace_houdini(
            program,
            trace_depth=5,
            trace_limit=100,
            models_per_prefix=1,
            timeout_ms=5_000,
            random_seed=1,
        )
        assert seed.status is HoudiniStatus.UNKNOWN
        assert trace.status is HoudiniStatus.SUCCESS
        assert trace.trace_result is not None


def test_trace_houdini_mutate_applies_to_combined_seed_and_trace_candidates() -> None:
    """--mut is not restricted to seed-mined or --cands candidates: when
    combined with --trace-houdini, mutate_candidates() is applied to the
    full seed-plus-trace candidate pool at whichever stage the pipeline
    reaches, not just to the syntactic seed candidates alone."""

    program = parse_chc_file(
        TRACE_EXAMPLES / "count_by_2_modular_safe.smt2", slice_program=False
    )
    plain = run_trace_houdini(
        program,
        trace_depth=5,
        trace_limit=100,
        models_per_prefix=1,
        timeout_ms=5_000,
        random_seed=1,
    )
    mutated = run_trace_houdini(
        program,
        trace_depth=5,
        trace_limit=100,
        models_per_prefix=1,
        timeout_ms=5_000,
        random_seed=1,
        mutate=True,
    )
    assert plain.mutation_result is None
    assert mutated.mutation_result is not None
    assert mutated.mutation_result.statistics.candidates_added > 0
    assert mutated.trace_result is not None
    assert mutated.status is HoudiniStatus.SUCCESS


def test_cli_mut_requires_a_candidate_source(capsys) -> None:
    with pytest.raises(SystemExit) as exc_info:
        main(["--mut", str(TRACE_EXAMPLES / "integer_affine_safe.smt2")])
    assert exc_info.value.code == 2
    assert "--mut requires" in capsys.readouterr().err


def test_cli_trace_houdini_mut_combination(capsys) -> None:
    path = LENGTH_EXAMPLES / "append_two_parity_safe.smt2"
    assert (
        main(
            [
                "--trace-houdini",
                "--mut",
                "--trace-depth",
                "6",
                "--trace-models-per-prefix",
                "1",
                "--json",
                str(path),
            ]
        )
        == 0
    )
    payload = json.loads(capsys.readouterr().out)
    assert payload["status"] == "success"
    assert payload["mutation"] is not None
    assert payload["mutation"]["candidates_added"] > 0
    assert payload["trace_mining"] is not None


def test_cli_trace_houdini_still_rejects_cands_and_validate_candidates() -> None:
    path = TRACE_EXAMPLES / "integer_affine_safe.smt2"
    cands_path = ROOT / "examples" / "cands" / "string_bounded_append_candidates.smt2"
    for extra_args in (
        ["--cands", str(cands_path)],
        ["--validate-candidates"],
    ):
        with pytest.raises(SystemExit) as exc_info:
            main(["--trace-houdini", *extra_args, str(path)])
        assert exc_info.value.code == 2


def test_cli_trace_houdini_accepts_redundant_seed_houdini(capsys) -> None:
    """--seed-houdini alongside --trace-houdini is accepted, not rejected:
    run_trace_houdini() already performs an ordinary seed-houdini attempt as
    its own first stage, so the combination is a redundant but harmless
    no-op rather than a usage error."""

    path = TRACE_EXAMPLES / "integer_affine_safe.smt2"
    assert (
        main(["--trace-houdini", "--seed-houdini", "--json", str(path)]) == 0
    )
    payload = json.loads(capsys.readouterr().out)
    assert payload["status"] == "success"


def test_mutate_candidates_max_terms_per_relation_bounds_pair_count() -> None:
    """max_terms_per_relation must bound pairing cost, not just filter the
    output afterward: without it, N equalities/inequalities produce O(N^2)
    pairs, which is exactly what made --trace-houdini --mut intractable on
    large trace-sampled candidate pools (see
    test_trace_houdini_mut_bounds_large_pools below)."""

    relation = z3.Function("bound_test_rel", z3.IntSort(), z3.BoolSort())
    x = z3.Int("x")
    # Powers of 3: pairwise sums essentially never coincide with another
    # power of 3, so derived candidates won't spuriously collide with the
    # originals the way an arithmetic progression's midpoints would (e.g.
    # x==0..x==9 derives x==1 from the (0,2) pair, which then gets filtered
    # as a duplicate of the already-present x==1 -- not a useful test of
    # what survives).
    candidates: CandidateMap = {relation: tuple(x == 3**n for n in range(40))}

    uncapped = mutate_candidates(candidates)
    capped = mutate_candidates(candidates, max_terms_per_relation=10)

    assert uncapped.statistics.equalities_considered == 40
    assert uncapped.statistics.terms_dropped_by_cap == 0
    assert capped.statistics.equalities_considered == 10
    # 30 dropped from the numeric-pairing list, and (since every one of
    # these 40 candidates is also a general/sort-agnostic equality, feeding
    # the separate equality-substitution mechanism) another 30 dropped from
    # that list too -- both lists draw from the same input here, so the
    # same 30-candidate truncation is counted once per list it applies to.
    assert capped.statistics.terms_dropped_by_cap == 60
    assert capped.statistics.general_equalities_considered == 10
    # C(10, 2) = 45 pairs vs C(40, 2) = 780: the cap must actually reduce
    # the pairing work, not just the reported count.
    assert capped.statistics.equality_pairs_combined == 45
    assert uncapped.statistics.equality_pairs_combined == 780
    assert capped.statistics.candidates_added < uncapped.statistics.candidates_added


def test_trace_houdini_mut_bounds_large_pools() -> None:
    """Regression test for a real-world case where --trace-houdini --mut
    took on the order of 30+ minutes: an array-tiling benchmark whose
    combined seed-plus-trace candidate pool runs to ~130 numeric
    equalities/inequalities for a single relation. Uncapped pairwise --mut
    combination over a pool that size produces tens of thousands of derived
    candidates, each independently expensive for MultiHoudini to verify
    against this program's Store/ite-heavy array rules. Runs via a
    subprocess with a hard wall-clock timeout so a regression here fails
    the test suite quickly instead of hanging it."""

    path = TRACE_EXAMPLES / "array_tiling_pr4.smt2"
    result = subprocess.run(
        [
            sys.executable,
            "-m",
            "pyhorn_bnd",
            "--trace-houdini",
            "--mut",
            "--debug",
            "--to",
            "500",
            str(path),
        ],
        cwd=ROOT,
        env={**os.environ, "PYTHONPATH": str(ROOT / "src")},
        capture_output=True,
        text=True,
        timeout=90,
        check=False,  # exit code 2 (unknown) is the expected, correct
        # outcome here, not a failure -- see the assertion below.
    )
    assert result.returncode == 2, result.stderr
    assert "Mutation:" in result.stdout
    mutation_line = next(
        line for line in result.stdout.splitlines() if line.startswith("Mutation:")
    )
    assert "capped=" in mutation_line


def test_mutate_candidates_general_equalities_respects_the_same_cap() -> None:
    """Regression test: general_equalities (which feeds sort-agnostic
    equality substitution) must be truncated by max_terms_per_relation the
    same way equalities/inequalities (which feed numeric pairing) already
    are. It previously wasn't -- substitution silently saw every equality
    in the pool regardless of the cap, which on a large synthetic pool
    (400 equalities x 400 other candidates) cost several seconds of pure
    Python loop overhead even with substitution's own attempt-count cap
    already engaged, since nothing broke out of the outer loops early."""

    relation = z3.Function("cap_test_rel", z3.IntSort(), z3.BoolSort())
    x = z3.Int("x")
    candidates: CandidateMap = {relation: tuple(x == 3**n for n in range(40))}

    result = mutate_candidates(candidates, max_terms_per_relation=5)
    assert result.statistics.general_equalities_considered == 5


def test_run_trace_houdini_mutate_stress_pool_is_fast() -> None:
    """The same regression at the run_trace_houdini() level, with a large
    enough synthetic pool that the pre-fix outer-loop overhead alone would
    have taken multiple seconds even with every cap correctly engaged
    everywhere else. Wall-clock bounded generously (5s, the fixed version
    should take well under 1s) so a real regression fails fast."""

    relation = z3.Function("stress_rel", z3.IntSort(), z3.StringSort(), z3.BoolSort())
    x = z3.Int("x")
    s = z3.String("s")
    eqs = tuple(x == 7**i for i in range(200)) + tuple(
        z3.Length(s) == 11**i for i in range(200)
    )
    other = tuple(x + i >= 0 for i in range(200)) + tuple(
        z3.Length(s) + i >= 0 for i in range(200)
    )
    candidates: CandidateMap = {relation: eqs + other}

    start = time.monotonic()
    result = mutate_candidates(candidates, max_terms_per_relation=3)
    elapsed = time.monotonic() - start
    assert elapsed < 5.0, f"mutate_candidates took {elapsed:.2f}s, expected < 5s"
    assert result.statistics.general_equalities_considered == 3


def test_cli_trace_mutation_substitution_limit_is_wired_through(capsys) -> None:
    """Regression test: max_equality_substitutions_per_relation previously
    had no CLI flag and was never passed from run_trace_houdini() to
    mutate_candidates() at all, so it silently always used its hardcoded
    default regardless of anything the user set. This checks the flag
    exists, is accepted, and actually changes the reported statistics --
    not just that the process exits 0."""

    path = TRACE_EXAMPLES / "integer_affine_safe.smt2"
    assert (
        main(
            [
                "--trace-houdini",
                "--mut",
                "--trace-mutation-substitution-limit",
                "1",
                "--json",
                str(path),
            ]
        )
        == 0
    )
    tight = json.loads(capsys.readouterr().out)

    assert (
        main(
            [
                "--trace-houdini",
                "--mut",
                "--trace-mutation-substitution-limit",
                "0",
                "--json",
                str(path),
            ]
        )
        == 0
    )
    unlimited = json.loads(capsys.readouterr().out)

    assert (
        tight["mutation"]["substitution_rewrites_attempted"]
        <= unlimited["mutation"]["substitution_rewrites_attempted"]
    )
    assert tight["mutation"]["substitution_rewrites_attempted"] <= 1
