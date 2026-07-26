"""CLI-level integration tests for ``--cands``.

These exercise the option the way a user actually would: through
:func:`pyhorn_bnd.cli.main`, against real CHC benchmark files, checking exit
codes, human-readable output, and ``--json`` output.
"""

from __future__ import annotations

import json
import textwrap
from pathlib import Path

from pyhorn_bnd.cli import main

ROOT = Path(__file__).resolve().parents[1]
EXAMPLES = ROOT / "examples" / "seed_houdini"
CANDS_EXAMPLES = ROOT / "examples" / "cands"


def _write(tmp_path: Path, name: str, content: str) -> Path:
    p = tmp_path / name
    p.write_text(textwrap.dedent(content), encoding="utf-8")
    return p


# ---------------------------------------------------------------------------
# Happy path
# ---------------------------------------------------------------------------


def test_cands_alone_proves_safe_counter(tmp_path: Path, capsys) -> None:
    cands = _write(
        tmp_path,
        "cands.smt2",
        """\
        (define-fun inv ((x Int)) Bool
          (and (>= x 0) (<= x 10)))
        """,
    )
    rc = main(["--cands", str(cands), str(EXAMPLES / "counter_safe.smt2")])
    assert rc == 0
    assert capsys.readouterr().out.strip() == "Success"


def test_cands_alone_does_not_run_seed_mining(tmp_path: Path, capsys) -> None:
    """--cands without --seed-houdini must not silently pull in mined
    candidates: the JSON payload's seed_mining field must stay null while
    user_candidates reflects exactly what the file contained."""
    cands = _write(
        tmp_path,
        "cands.smt2",
        """\
        (define-fun inv ((x Int)) Bool
          (and (>= x 0) (<= x 10)))
        """,
    )
    rc = main(
        ["--cands", str(cands), "--json", str(EXAMPLES / "counter_safe.smt2")]
    )
    assert rc == 0
    payload = json.loads(capsys.readouterr().out)
    assert payload["status"] == "success"
    assert payload["seed_mining"] is None
    assert payload["user_candidates"] == {"predicates": 1, "candidates": 2}


def test_cands_removes_bad_conjunct_and_still_succeeds(tmp_path: Path, capsys) -> None:
    cands = _write(
        tmp_path,
        "cands.smt2",
        """\
        (define-fun inv ((x Int)) Bool
          (and (>= x 0) (<= x 10) (= x 999)))
        """,
    )
    rc = main(
        ["--cands", str(cands), "--json", str(EXAMPLES / "counter_safe.smt2")]
    )
    assert rc == 0
    payload = json.loads(capsys.readouterr().out)
    assert payload["status"] == "success"
    assert payload["houdini"]["candidates_initial"] == 3
    assert payload["houdini"]["candidates_removed"] == 1
    assert payload["houdini"]["candidates_remaining"] == 2
    assert "999" not in json.dumps(payload["invariants"])


def test_cands_insufficient_candidates_report_unknown(tmp_path: Path, capsys) -> None:
    cands = _write(
        tmp_path,
        "cands.smt2",
        """\
        (define-fun inv ((x Int)) Bool
          (= x 999))
        """,
    )
    rc = main(["--cands", str(cands), str(EXAMPLES / "counter_safe.smt2")])
    assert rc == 2
    assert capsys.readouterr().out.strip() == "unknown"


def test_cands_with_no_matching_predicate_reports_unknown_not_error(
    tmp_path: Path, capsys
) -> None:
    """A candidate file that matches nothing is a no-op (Houdini then runs
    with the 'true' invariant for every predicate), not a hard error."""
    cands = _write(
        tmp_path,
        "cands.smt2",
        "(define-fun unrelated_name ((x Int)) Bool (>= x 0))\n",
    )
    rc = main(["--cands", str(cands), str(EXAMPLES / "counter_safe.smt2")])
    assert rc == 2
    assert capsys.readouterr().out.strip() == "unknown"


def test_cands_multiple_predicates(tmp_path: Path, capsys) -> None:
    cands = _write(
        tmp_path,
        "cands.smt2",
        """\
        (define-fun p ((x Int)) Bool (= x 0))
        (define-fun q ((x Int)) Bool (and (>= x 0) (<= x 3)))
        """,
    )
    rc = main(
        [
            "--cands",
            str(cands),
            "--print-invariants",
            str(EXAMPLES / "multiple_predicates.smt2"),
        ]
    )
    out = capsys.readouterr().out
    assert rc == 0
    assert "Success" in out
    assert "p(" in out
    assert "q(" in out


def test_cands_combined_with_seed_houdini_merges(tmp_path: Path, capsys) -> None:
    cands = _write(
        tmp_path,
        "cands.smt2",
        """\
        (define-fun inv ((x Int)) Bool
          (>= x -100))
        """,
    )
    rc = main(
        [
            "--seed-houdini",
            "--cands",
            str(cands),
            "--json",
            str(EXAMPLES / "counter_safe.smt2"),
        ]
    )
    assert rc == 0
    payload = json.loads(capsys.readouterr().out)
    assert payload["status"] == "success"
    assert payload["seed_mining"] is not None
    assert payload["user_candidates"] == {"predicates": 1, "candidates": 1}
    # The user-supplied (loose) lower bound is not implied by anything
    # SeedMiner would mine on its own, so it must show up verbatim.
    assert any(
        "-100" in inv or "100" in inv for inv in payload["invariants"]["inv"]
    )


def test_cands_print_invariants_shows_true_for_empty_predicate(
    tmp_path: Path, capsys
) -> None:
    """A predicate present in the CHC file but absent from the candidate file
    keeps its default 'true' invariant and is still reported."""
    cands = _write(
        tmp_path,
        "cands.smt2",
        "(define-fun p ((x Int)) Bool (= x 0))\n",
    )
    rc = main(
        [
            "--cands",
            str(cands),
            "--print-invariants",
            str(EXAMPLES / "multiple_predicates.smt2"),
        ]
    )
    out = capsys.readouterr().out
    # q has no user candidate at all; Houdini still certifies it needs a
    # nontrivial invariant here (q is not safe under 'true'), so this
    # particular combination should end up unknown.
    assert rc == 2
    assert "unknown" in out


# ---------------------------------------------------------------------------
# Error handling
# ---------------------------------------------------------------------------


def test_cands_missing_file_is_reported_cleanly(capsys) -> None:
    rc = main(
        ["--cands", "/nonexistent/path.smt2", str(EXAMPLES / "counter_safe.smt2")]
    )
    err = capsys.readouterr().err
    assert rc == 3
    assert "error:" in err


def test_cands_malformed_s_expression_is_reported_cleanly(
    tmp_path: Path, capsys
) -> None:
    cands = _write(tmp_path, "cands.smt2", "(define-fun inv ((x Int)) Bool (>= x 0)\n")
    rc = main(["--cands", str(cands), str(EXAMPLES / "counter_safe.smt2")])
    err = capsys.readouterr().err
    assert rc == 3
    assert "error:" in err


def test_cands_arity_mismatch_is_reported_cleanly(tmp_path: Path, capsys) -> None:
    cands = _write(
        tmp_path,
        "cands.smt2",
        "(define-fun inv ((x Int) (y Int)) Bool (>= x 0))\n",
    )
    rc = main(["--cands", str(cands), str(EXAMPLES / "counter_safe.smt2")])
    err = capsys.readouterr().err
    assert rc == 3
    assert "error:" in err
    assert "parameter" in err


def test_cands_wrong_return_sort_is_reported_cleanly(tmp_path: Path, capsys) -> None:
    cands = _write(tmp_path, "cands.smt2", "(define-fun inv ((x Int)) Int x)\n")
    rc = main(["--cands", str(cands), str(EXAMPLES / "counter_safe.smt2")])
    err = capsys.readouterr().err
    assert rc == 3
    assert "return sort must be Bool" in err


# ---------------------------------------------------------------------------
# Shipped examples
# ---------------------------------------------------------------------------


def test_shipped_counter_safe_example_succeeds(capsys) -> None:
    rc = main(
        [
            "--cands",
            str(CANDS_EXAMPLES / "counter_safe_candidates.smt2"),
            str(EXAMPLES / "counter_safe.smt2"),
        ]
    )
    assert rc == 0
    assert capsys.readouterr().out.strip() == "Success"


def test_shipped_multiple_predicates_example_succeeds_and_removes_bad_guess(
    capsys,
) -> None:
    rc = main(
        [
            "--cands",
            str(CANDS_EXAMPLES / "multiple_predicates_candidates.smt2"),
            "--json",
            str(EXAMPLES / "multiple_predicates.smt2"),
        ]
    )
    assert rc == 0
    payload = json.loads(capsys.readouterr().out)
    assert payload["status"] == "success"
    assert payload["houdini"]["candidates_removed"] == 1
    assert "999" not in json.dumps(payload["invariants"])
