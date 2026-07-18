from __future__ import annotations

import os
from pathlib import Path

import pytest

from pyhorn_bnd import parse_chc_file

ROOT = Path(__file__).resolve().parents[1]
MANIFEST = ROOT / "tests" / "data" / "bench_horn_manifest.txt"
CORPUS_ENV = "PYHORN_BENCH_HORN_DIR"


def _corpus_directory() -> Path:
    configured = os.environ.get(CORPUS_ENV)
    if not configured:
        pytest.skip(
            f"set {CORPUS_ENV} to run the external 352-file parser regression"
        )
    directory = Path(configured)
    if not directory.is_dir():
        pytest.fail(f"{CORPUS_ENV} is not a directory: {directory}")
    return directory


def _validate_relation_arguments(program) -> None:
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


@pytest.mark.corpus
def test_complete_bench_horn_corpus_parses_and_has_expected_linear_shape() -> None:
    directory = _corpus_directory()
    expected_names = {
        line.strip()
        for line in MANIFEST.read_text(encoding="utf-8").splitlines()
        if line.strip()
    }
    assert len(expected_names) == 352

    files = sorted(directory.glob("*.smt2"))
    actual_names = {path.name for path in files}
    missing = sorted(expected_names - actual_names)
    assert not missing, f"missing manifest files: {missing}"

    failures: list[str] = []
    for path in files:
        try:
            program = parse_chc_file(path, slice_program=False)
            assert len(program.rules) == 3
            assert len(program.relations) == 2
            assert len(program.query_relations) == 1
            assert sum(rule.is_fact for rule in program.rules) == 1
            assert sum(rule.is_inductive for rule in program.rules) == 1
            assert sum(rule.is_query for rule in program.rules) == 1
            assert all(relation.arity() == 0 for relation in program.query_relations)
            assert tuple(rule.rule_id for rule in program.rules) == (0, 1, 2)
            _validate_relation_arguments(program)
        except Exception as exc:  # collect the full corpus failure set
            failures.append(f"{path.name}: {type(exc).__name__}: {exc}")

    assert not failures, "\n".join(failures)
