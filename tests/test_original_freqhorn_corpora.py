from __future__ import annotations

import os
from pathlib import Path

import pytest

from pyhorn_bnd import parse_chc_file

EXPECTED = {
    "bench_horn": (352, 1_056),
    "bench_horn_cex": (79, 435),
    "bench_horn_multiple": (176, 953),
}


@pytest.mark.corpus
def test_all_original_freqhorn_suites_parse() -> None:
    configured = os.environ.get("PYHORN_FREQHORN_ROOT")
    if configured is None:
        pytest.skip("set PYHORN_FREQHORN_ROOT to the original FreqHorn repository")
    root = Path(configured)

    for suite, (expected_files, expected_rules) in EXPECTED.items():
        files = sorted((root / suite).glob("*.smt2"))
        assert len(files) == expected_files
        rules = 0
        for path in files:
            program = parse_chc_file(path, slice_program=False)
            rules += len(program.rules)
        assert rules == expected_rules
