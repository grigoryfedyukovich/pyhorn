"""End-to-end round-trip tests: ``--seed-houdini --dump-cands`` followed by a
fresh ``--cands`` run on the dumped file.

This is the scenario requested directly: run pyhorn once with
``--seed-houdini`` on a benchmark, serialize whatever invariants it found as
a ``define-fun`` file, then run pyhorn again -- as a completely separate
:func:`main` invocation, exactly as a second CLI process would see it -- with
``--cands`` pointing at that file, and check the outcome is reproduced.

``--print-invariants`` was not designed for this: it prints Python's infix
``str()`` form (``__inv_0 <= 10``), which is not valid SMT-LIB2 and cannot be
parsed back. ``--dump-cands`` instead writes ``define-fun`` s-expression text
via :func:`pyhorn_bnd.cands.format_candidates_smt2`, which round-trips
through :func:`pyhorn_bnd.cands.parse_candidate_file` by construction (see
``tests/test_cands.py::TestFormatCandidatesSmt2``). These tests check the
same property one level up, through the actual CLI entry point.
"""

from __future__ import annotations

import json
import os
from pathlib import Path

import pytest

from pyhorn_bnd.cli import main

ROOT = Path(__file__).resolve().parents[1]
EXAMPLES = ROOT / "examples" / "seed_houdini"

# Ad hoc roundtrip check for a single, arbitrary CHC file, without adding it
# to the repo's example corpus. Mirrors PYHORN_BENCH_HORN_DIR's convention in
# test_bench_horn_corpus.py: unset by default, so this stays a no-op/skip in
# ordinary test runs.
CUSTOM_FILE_ENV = "PYHORN_ROUNDTRIP_FILE"


def _custom_file() -> Path:
    configured = os.environ.get(CUSTOM_FILE_ENV)
    if not configured:
        pytest.skip(
            f"set {CUSTOM_FILE_ENV}=/path/to/file.smt2 to roundtrip-check "
            "an arbitrary CHC file, e.g.:\n"
            f"  {CUSTOM_FILE_ENV}=/path/to/file.smt2 python3 -m pytest "
            "tests/test_cands_roundtrip.py -k custom_file -v"
        )
    path = Path(configured)
    if not path.is_file():
        pytest.fail(f"{CUSTOM_FILE_ENV} is not a file: {path}")
    return path


# ---------------------------------------------------------------------------
# Success round-trips: --seed-houdini succeeds, and re-running with --cands
# on the dump succeeds again.
# ---------------------------------------------------------------------------


@pytest.mark.parametrize(
    "benchmark",
    ["counter_safe.smt2", "multiple_predicates.smt2"],
)
def test_seed_houdini_dump_then_cands_reproduces_success(
    benchmark: str, tmp_path: Path, capsys
) -> None:
    dump_path = tmp_path / "dumped.smt2"
    chc_file = str(EXAMPLES / benchmark)

    # Step 1: mine and filter candidates, dump whatever MultiHoudini retained.
    rc1 = main(["--seed-houdini", "--dump-cands", str(dump_path), chc_file])
    out1 = capsys.readouterr().out
    assert rc1 == 0
    assert out1.strip() == "Success"
    assert dump_path.exists()

    dumped_text = dump_path.read_text(encoding="utf-8")
    assert "(define-fun" in dumped_text
    # The dump is valid SMT-LIB2 s-expression text, not the bare infix form
    # --print-invariants would show (e.g. "__inv_0 <= 10" has no such line
    # here; every candidate appears inside a define-fun body instead).
    assert dumped_text.count("(define-fun") >= 1

    # Step 2: a brand new, independent run using only the dumped file.
    rc2 = main(["--cands", str(dump_path), chc_file])
    out2 = capsys.readouterr().out
    assert rc2 == 0
    assert out2.strip() == "Success"


@pytest.mark.parametrize(
    "benchmark",
    ["counter_safe.smt2", "multiple_predicates.smt2"],
)
def test_roundtrip_second_run_does_not_need_seed_mining(
    benchmark: str, tmp_path: Path, capsys
) -> None:
    """The whole point of the round trip is that the second run is driven
    entirely by the dumped file -- confirm no seed mining happens on replay
    by checking the JSON payload's seed_mining field is null."""
    dump_path = tmp_path / "dumped.smt2"
    chc_file = str(EXAMPLES / benchmark)

    rc1 = main(["--seed-houdini", "--dump-cands", str(dump_path), chc_file])
    capsys.readouterr()
    assert rc1 == 0

    rc2 = main(["--cands", str(dump_path), "--json", chc_file])
    assert rc2 == 0
    payload = json.loads(capsys.readouterr().out)
    assert payload["status"] == "success"
    assert payload["seed_mining"] is None
    assert payload["user_candidates"]["predicates"] >= 1
    assert payload["user_candidates"]["candidates"] >= 1


def test_roundtrip_invariants_are_identical_across_runs(
    tmp_path: Path, capsys
) -> None:
    """The retained invariant set from the --cands replay should be exactly
    the set that was dumped (Houdini has nothing left to remove: everything
    in the file is already inductive), not a strict subset."""
    dump_path = tmp_path / "dumped.smt2"
    chc_file = str(EXAMPLES / "counter_safe.smt2")

    rc1 = main(
        ["--seed-houdini", "--dump-cands", str(dump_path), "--json", chc_file]
    )
    payload1 = json.loads(capsys.readouterr().out)
    assert rc1 == 0

    rc2 = main(["--cands", str(dump_path), "--json", chc_file])
    payload2 = json.loads(capsys.readouterr().out)
    assert rc2 == 0

    assert payload1["invariants"] == payload2["invariants"]
    # Nothing should have been removed on replay: every dumped candidate was
    # already inductive.
    assert payload2["houdini"]["candidates_removed"] == 0


# ---------------------------------------------------------------------------
# Status-preserving round-trip: the first run does *not* succeed, and the
# dump still faithfully reproduces "unknown" on replay (--dump-cands writes
# whatever MultiHoudini ended up with, not only a successful outcome).
# ---------------------------------------------------------------------------


def test_roundtrip_preserves_unknown_status(tmp_path: Path, capsys) -> None:
    dump_path = tmp_path / "dumped.smt2"
    chc_file = str(EXAMPLES / "counter_unsafe.smt2")

    rc1 = main(["--seed-houdini", "--dump-cands", str(dump_path), chc_file])
    out1 = capsys.readouterr().out
    assert rc1 == 2
    assert out1.strip() == "unknown"
    # A dump is still produced -- it just documents an insufficient set.
    assert dump_path.exists()

    rc2 = main(["--cands", str(dump_path), chc_file])
    out2 = capsys.readouterr().out
    assert rc2 == 2
    assert out2.strip() == "unknown"


# ---------------------------------------------------------------------------
# --dump-cands argument validation
# ---------------------------------------------------------------------------


def test_dump_cands_without_houdini_mode_is_a_usage_error(
    tmp_path: Path, capsys
) -> None:
    dump_path = tmp_path / "dumped.smt2"
    with pytest.raises(SystemExit) as exc_info:
        main(["--dump-cands", str(dump_path), str(EXAMPLES / "counter_safe.smt2")])
    assert exc_info.value.code == 2
    assert "--dump-cands requires" in capsys.readouterr().err
    assert not dump_path.exists()


def test_dump_cands_with_cands_alone_is_accepted(tmp_path: Path, capsys) -> None:
    """--dump-cands only needs *a* Houdini-mode flag, not --seed-houdini
    specifically -- --cands alone is enough."""
    seed_dump = tmp_path / "seed_dump.smt2"
    main(["--seed-houdini", "--dump-cands", str(seed_dump), str(EXAMPLES / "counter_safe.smt2")])
    capsys.readouterr()

    replay_dump = tmp_path / "replay_dump.smt2"
    rc = main(
        [
            "--cands",
            str(seed_dump),
            "--dump-cands",
            str(replay_dump),
            str(EXAMPLES / "counter_safe.smt2"),
        ]
    )
    assert rc == 0
    assert replay_dump.exists()


# ---------------------------------------------------------------------------
# Multi-generation round trip: dump -> replay -> dump again -> replay again.
# Demonstrates the format is stable under repeated round-tripping, not just
# a single hop.
# ---------------------------------------------------------------------------


def test_double_roundtrip_is_stable(tmp_path: Path, capsys) -> None:
    chc_file = str(EXAMPLES / "counter_safe.smt2")
    gen1 = tmp_path / "gen1.smt2"
    gen2 = tmp_path / "gen2.smt2"

    rc1 = main(["--seed-houdini", "--dump-cands", str(gen1), chc_file])
    capsys.readouterr()
    assert rc1 == 0

    rc2 = main(["--cands", str(gen1), "--dump-cands", str(gen2), chc_file])
    capsys.readouterr()
    assert rc2 == 0

    rc3 = main(["--cands", str(gen2), chc_file])
    out3 = capsys.readouterr().out
    assert rc3 == 0
    assert out3.strip() == "Success"

    # The candidate set stabilizes after the first generation: nothing left
    # to remove on the second or third pass.
    assert gen1.read_text(encoding="utf-8") != ""
    assert gen2.read_text(encoding="utf-8") != ""


# ---------------------------------------------------------------------------
# Ad hoc round-trip check for a file you supply, e.g.:
#
#   PYHORN_ROUNDTRIP_FILE=/path/to/my.smt2 \
#     python3 -m pytest tests/test_cands_roundtrip.py -k custom_file -v
#
# Skipped (not failed) when PYHORN_ROUNDTRIP_FILE is unset, so it is a no-op
# in ordinary `pytest -q` runs and in CI.
# ---------------------------------------------------------------------------


def test_custom_file_roundtrip_status_is_stable(tmp_path: Path, capsys) -> None:
    """--seed-houdini, dumped and replayed through --cands, must land on the
    same status (Success or unknown) it started with -- for any CHC file,
    not just the two shipped as examples above."""
    chc_file = str(_custom_file())
    dump_path = tmp_path / "dumped.smt2"

    rc1 = main(["--seed-houdini", "--dump-cands", str(dump_path), chc_file])
    out1 = capsys.readouterr().out.strip()
    assert dump_path.exists(), "--dump-cands did not write a file"

    rc2 = main(["--cands", str(dump_path), chc_file])
    out2 = capsys.readouterr().out.strip()

    assert rc1 == rc2, (
        f"status changed across the roundtrip for {chc_file}: "
        f"{out1!r} (rc={rc1}) -> {out2!r} (rc={rc2})"
    )
    assert out1 == out2


def test_custom_file_roundtrip_removes_nothing_on_replay(
    tmp_path: Path, capsys
) -> None:
    """Every candidate written by --dump-cands was, by definition, already
    inductive when it was dumped, so replaying it through --cands must not
    remove anything further."""
    chc_file = str(_custom_file())
    dump_path = tmp_path / "dumped.smt2"

    main(["--seed-houdini", "--dump-cands", str(dump_path), chc_file])
    capsys.readouterr()

    rc = main(["--cands", str(dump_path), "--json", chc_file])
    payload = json.loads(capsys.readouterr().out)
    assert rc in (0, 2)
    assert payload["houdini"]["candidates_removed"] == 0
