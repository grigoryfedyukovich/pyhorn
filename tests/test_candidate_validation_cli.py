"""CLI-level integration tests for --validate-candidates / --candidate-bound."""

from __future__ import annotations

import json
import textwrap
from pathlib import Path

import pytest

from pyhorn_bnd.cli import main

ROOT = Path(__file__).resolve().parents[1]
EXAMPLES = ROOT / "examples" / "seed_houdini"


def _write(tmp_path: Path, name: str, content: str) -> Path:
    p = tmp_path / name
    p.write_text(textwrap.dedent(content), encoding="utf-8")
    return p


# ---------------------------------------------------------------------------
# Validation / usage errors
# ---------------------------------------------------------------------------


def test_validate_candidates_without_houdini_mode_is_a_usage_error(capsys) -> None:
    with pytest.raises(SystemExit) as exc_info:
        main(["--validate-candidates", str(EXAMPLES / "counter_safe.smt2")])
    assert exc_info.value.code == 2
    assert "--validate-candidates requires" in capsys.readouterr().err


def test_candidate_bound_zero_is_a_usage_error(capsys) -> None:
    with pytest.raises(SystemExit) as exc_info:
        main(
            [
                "--seed-houdini",
                "--validate-candidates",
                "--candidate-bound",
                "0",
                str(EXAMPLES / "counter_safe.smt2"),
            ]
        )
    assert exc_info.value.code == 2
    assert "--candidate-bound must be at least 1" in capsys.readouterr().err


def test_candidate_bound_without_validate_candidates_is_accepted_and_unused(capsys) -> None:
    """--candidate-bound alone (no --validate-candidates) is not an error -- it simply has
    nothing to configure."""
    rc = main(
        [
            "--seed-houdini",
            "--candidate-bound",
            "3",
            str(EXAMPLES / "counter_safe.smt2"),
        ]
    )
    assert rc == 0
    assert capsys.readouterr().out.strip() == "Success"


# ---------------------------------------------------------------------------
# Human-readable --debug output
# ---------------------------------------------------------------------------


def test_validate_candidates_debug_shows_confirmed_real_for_reachable_witness(capsys) -> None:
    rc = main(
        [
            "--seed-houdini",
            "--validate-candidates",
            "--debug",
            str(EXAMPLES / "counter_safe.smt2"),
        ]
    )
    err = capsys.readouterr().err
    assert rc == 0
    assert "check: confirmed real" in err
    assert "falsified by a reachable state at depth" in err


def test_validate_candidates_debug_shows_base_case_for_fact_rule(capsys) -> None:
    rc = main(
        [
            "--seed-houdini",
            "--validate-candidates",
            "--debug",
            str(EXAMPLES / "counter_safe.smt2"),
        ]
    )
    err = capsys.readouterr().err
    assert rc == 0
    assert "check: confirmed real (base case, always reachable)" in err


def test_validate_candidates_debug_shows_potentially_promising(tmp_path: Path, capsys) -> None:
    source = _write(
        tmp_path,
        "helper_lemma.smt2",
        """\
        (declare-var x Int)
        (declare-var y Int)
        (declare-rel inv (Int Int))
        (declare-rel fail ())
        (rule (inv 0 100))
        (rule (=> (and (inv x y) (< x 5)) (inv (+ x 1) (- y 1))))
        (rule (=> (and (inv x y) (>= x 5) (< y 90)) fail))
        """,
    )
    cands = _write(tmp_path, "cands.smt2", "(define-fun inv ((x Int) (y Int)) Bool (>= y 1))\n")

    rc = main(
        ["--cands", str(cands), "--validate-candidates", "--debug", str(source)]
    )
    err = capsys.readouterr().err
    assert rc == 2  # weak candidate alone does not prove the query safe
    assert "potentially promising" in err
    assert "may need a helper lemma" in err


def test_validate_candidates_without_flag_omits_check_line(capsys) -> None:
    """Without --validate-candidates, dropped candidates are still shown in
    --debug, but with no 'check:' verdict line (unchanged from before this
    feature existed)."""
    rc = main(
        ["--seed-houdini", "--debug", str(EXAMPLES / "counter_safe.smt2")]
    )
    err = capsys.readouterr().err
    assert rc == 0
    assert "Dropped candidates" in err
    assert "check:" not in err


# ---------------------------------------------------------------------------
# --json output
# ---------------------------------------------------------------------------


def test_validate_candidates_json_includes_candidate_validation_per_removed_candidate(capsys) -> None:
    rc = main(
        [
            "--seed-houdini",
            "--validate-candidates",
            "--json",
            str(EXAMPLES / "counter_safe.smt2"),
        ]
    )
    assert rc == 0
    payload = json.loads(capsys.readouterr().out)
    removed = payload["removed_candidates"]
    assert len(removed) > 0
    for entry in removed:
        assert entry["candidate_validation"] is not None
        assert entry["candidate_validation"]["status"] in {
            "reachable",
            "not-found",
            "unknown",
            "not-applicable",
        }


def test_validate_candidates_json_witness_depth_matches_expected_for_x_equals_9(capsys) -> None:
    """Falsifying 'x < 10' requires reaching inv with x=10 directly (1 fact
    + 10 self-loop steps = depth 11), not the x=9 pre-state Houdini itself
    reported -- the default --candidate-bound (10) is one short of it, so this
    needs --candidate-bound 11 explicitly."""
    rc = main(
        [
            "--seed-houdini",
            "--validate-candidates",
            "--candidate-bound",
            "11",
            "--json",
            str(EXAMPLES / "counter_safe.smt2"),
        ]
    )
    assert rc == 0
    payload = json.loads(capsys.readouterr().out)
    entry = next(
        e for e in payload["removed_candidates"] if e["pre_state"] == "__inv_0 = 9"
    )
    assert entry["candidate_validation"]["status"] == "reachable"
    assert entry["candidate_validation"]["witness_depth"] == 11


def test_validate_candidates_default_bound_does_not_find_the_x_equals_9_witness(
    capsys,
) -> None:
    """Direct regression guard for the above: the default --candidate-bound (10)
    is one short of the depth-11 witness, so this specific removal comes
    back not-found rather than reachable with the CLI's own default."""
    rc = main(
        [
            "--seed-houdini",
            "--validate-candidates",
            "--json",
            str(EXAMPLES / "counter_safe.smt2"),
        ]
    )
    assert rc == 0  # --validate-candidates is a post-hoc diagnostic; it never
    # changes which candidates Houdini itself retained or certified
    payload = json.loads(capsys.readouterr().out)
    entry = next(
        e for e in payload["removed_candidates"] if e["pre_state"] == "__inv_0 = 9"
    )
    assert entry["candidate_validation"]["status"] == "not-found"
    assert entry["candidate_validation"]["checked_upto"] == 10


def test_json_without_validate_candidates_has_null_candidate_validation(capsys) -> None:
    rc = main(
        ["--seed-houdini", "--json", str(EXAMPLES / "counter_safe.smt2")]
    )
    assert rc == 0
    payload = json.loads(capsys.readouterr().out)
    removed = payload["removed_candidates"]
    assert len(removed) > 0
    assert all(entry["candidate_validation"] is None for entry in removed)


def test_candidate_bound_is_reflected_in_json_checked_upto(capsys) -> None:
    rc = main(
        [
            "--seed-houdini",
            "--validate-candidates",
            "--candidate-bound",
            "3",
            "--json",
            str(EXAMPLES / "counter_safe.smt2"),
        ]
    )
    assert rc == 0
    payload = json.loads(capsys.readouterr().out)
    entry = next(
        e for e in payload["removed_candidates"] if e["pre_state"] == "__inv_0 = 9"
    )
    # x=9 genuinely requires depth 11 (see the dedicated depth tests);
    # bounded to 3, it must not be found either way.
    assert entry["candidate_validation"]["status"] == "not-found"
    assert entry["candidate_validation"]["checked_upto"] == 3


# ---------------------------------------------------------------------------
# --dump-promising-candidates
# ---------------------------------------------------------------------------


def test_dump_promising_candidates_requires_validate_candidates(tmp_path: Path, capsys) -> None:
    out_dir = tmp_path / "cti_files"
    with pytest.raises(SystemExit) as exc_info:
        main(
            [
                "--seed-houdini",
                "--dump-promising-candidates",
                str(out_dir),
                str(EXAMPLES / "counter_safe.smt2"),
            ]
        )
    assert exc_info.value.code == 2
    assert "--dump-promising-candidates requires --validate-candidates" in capsys.readouterr().err
    assert not out_dir.exists()


def _helper_lemma_source(tmp_path: Path) -> Path:
    return _write(
        tmp_path,
        "helper_lemma.smt2",
        """\
        (declare-var x Int)
        (declare-var y Int)
        (declare-rel inv (Int Int))
        (declare-rel fail ())
        (rule (inv 0 100))
        (rule (=> (and (inv x y) (< x 5)) (inv (+ x 1) (- y 1))))
        (rule (=> (and (inv x y) (>= x 5) (< y 90)) fail))
        """,
    )


def test_dump_promising_candidates_writes_a_file_for_the_weak_candidate(
    tmp_path: Path, capsys
) -> None:
    source = _helper_lemma_source(tmp_path)
    cands = _write(
        tmp_path, "cands.smt2", "(define-fun inv ((x Int) (y Int)) Bool (>= y 1))\n"
    )
    out_dir = tmp_path / "cti_files"

    rc = main(
        [
            "--cands",
            str(cands),
            "--validate-candidates",
            "--dump-promising-candidates",
            str(out_dir),
            str(source),
        ]
    )
    assert rc == 2  # weak candidate alone does not prove the query safe
    files = list(out_dir.glob("*.smt2"))
    assert len(files) == 1
    content = files[0].read_text(encoding="utf-8")
    assert "(set-logic HORN)" in content
    assert "(declare-fun inv (Int Int) Bool)" in content
    assert "fail" not in content
    assert "(check-sat)" in content


def test_dump_promising_candidates_reports_written_count_in_debug(
    tmp_path: Path, capsys
) -> None:
    source = _helper_lemma_source(tmp_path)
    cands = _write(
        tmp_path, "cands.smt2", "(define-fun inv ((x Int) (y Int)) Bool (>= y 1))\n"
    )
    out_dir = tmp_path / "cti_files"

    main(
        [
            "--cands",
            str(cands),
            "--validate-candidates",
            "--dump-promising-candidates",
            str(out_dir),
            "--debug",
            str(source),
        ]
    )
    captured = capsys.readouterr()
    assert (
        f"Validation: wrote 1 potentially-promising verification file(s) to {out_dir}"
        in captured.out
    )
    assert "file: " in captured.err  # per-candidate path shown next to the check: line


def test_dump_promising_candidates_json_includes_verification_file_path(
    tmp_path: Path, capsys
) -> None:
    source = _helper_lemma_source(tmp_path)
    cands = _write(
        tmp_path, "cands.smt2", "(define-fun inv ((x Int) (y Int)) Bool (>= y 1))\n"
    )
    out_dir = tmp_path / "cti_files"

    main(
        [
            "--cands",
            str(cands),
            "--validate-candidates",
            "--dump-promising-candidates",
            str(out_dir),
            "--json",
            str(source),
        ]
    )
    payload = json.loads(capsys.readouterr().out)
    entry = payload["removed_candidates"][0]
    assert entry["candidate_validation"]["status"] == "not-found"
    assert entry["verification_file"] is not None
    assert Path(entry["verification_file"]).exists()
    assert Path(entry["verification_file"]).parent == out_dir


def test_no_files_written_when_every_removed_candidate_is_confirmed_real(
    tmp_path: Path, capsys
) -> None:
    """counter_safe.smt2's removed candidates are all REACHABLE or
    NOT_APPLICABLE (fact rule) once the bound covers the deepest one (the
    'x < 10' removal needs depth 11) -- none NOT_FOUND -- so the directory
    is created but stays empty."""
    out_dir = tmp_path / "cti_files"
    rc = main(
        [
            "--seed-houdini",
            "--validate-candidates",
            "--candidate-bound",
            "11",
            "--dump-promising-candidates",
            str(out_dir),
            str(EXAMPLES / "counter_safe.smt2"),
        ]
    )
    assert rc == 0
    assert out_dir.exists()
    assert list(out_dir.glob("*.smt2")) == []


def test_dump_promising_candidates_file_independently_reparses_and_is_bounded_safe(
    tmp_path: Path, capsys
) -> None:
    """End-to-end: the file written by the CLI is not just present, it is
    valid input this tool can independently re-check via plain bounded
    exploration (no Houdini), confirming the 'potentially promising'
    verdict was correct."""
    from pyhorn_bnd import parse_chc_file
    from pyhorn_bnd.explorer import BoundedExplorer, ExplorationStatus

    source = _helper_lemma_source(tmp_path)
    cands = _write(
        tmp_path, "cands.smt2", "(define-fun inv ((x Int) (y Int)) Bool (>= y 1))\n"
    )
    out_dir = tmp_path / "cti_files"

    main(
        [
            "--cands",
            str(cands),
            "--validate-candidates",
            "--dump-promising-candidates",
            str(out_dir),
            str(source),
        ]
    )
    capsys.readouterr()

    generated = next(out_dir.glob("*.smt2"))
    reparsed = parse_chc_file(generated, slice_program=False)
    explorer = BoundedExplorer(reparsed, timeout_ms=5_000)
    result = explorer.explore(upto=10)
    assert result.status is ExplorationStatus.BOUNDED_SAFE
