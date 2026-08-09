"""``cands.py`` (parse_candidate_file / format_candidates_smt2 / --dump-cands
round-trips) over Real, String, and mixed theories.

``tests/test_cands.py`` and ``tests/test_cands_cli.py`` exercise
``parse_candidate_file`` thoroughly at the unit level, and
``tests/test_cands_roundtrip.py`` exercises the ``--seed-houdini
--dump-cands`` then ``--cands`` round trip end to end -- but every fixture
in all three files uses ``z3.IntSort()`` predicates. This file mirrors
those same patterns for Real, String, and Real+String/Int+Real+String
predicate signatures, since positional parameter binding in ``cands.py``
is sort-generic by construction (see its module docstring) but was never
actually exercised here for anything but Int.
"""

from __future__ import annotations

import json
import textwrap
from pathlib import Path

import z3

from pyhorn_bnd.cands import parse_candidate_file
from pyhorn_bnd.cli import main

ROOT = Path(__file__).resolve().parents[1]
REAL = ROOT / "examples" / "real_arithmetic"
STRINGS = ROOT / "examples" / "string_theory"
MIXED = ROOT / "examples" / "mixed_theories"
CANDS = ROOT / "examples" / "cands"


def _rel(name: str, *sorts: z3.SortRef) -> z3.FuncDeclRef:
    return z3.Function(name, *sorts, z3.BoolSort())


def _write(tmp_path: Path, content: str) -> Path:
    p = tmp_path / "cands.smt2"
    p.write_text(textwrap.dedent(content), encoding="utf-8")
    return p


def _sexprs(cands: tuple[z3.BoolRef, ...]) -> set[str]:
    return {c.sexpr() for c in cands}


# ---------------------------------------------------------------------------
# parse_candidate_file -- Real
# ---------------------------------------------------------------------------


def test_parse_candidate_file_binds_real_parameters(tmp_path: Path) -> None:
    x = z3.Real("x")
    rel = _rel("inv", z3.RealSort())
    variables = {rel: (x,)}
    p = _write(
        tmp_path,
        """\
        (define-fun inv ((x Real)) Bool
          (and (<= x 10.0) (>= x 0.0)))
        """,
    )
    result = parse_candidate_file(p, variables)
    assert set(result.keys()) == {rel}
    sexprs = _sexprs(result[rel])
    assert z3.simplify(x <= 10.0).sexpr() in sexprs
    assert z3.simplify(x >= 0.0).sexpr() in sexprs


# ---------------------------------------------------------------------------
# parse_candidate_file -- String
# ---------------------------------------------------------------------------


def test_parse_candidate_file_binds_string_parameters(tmp_path: Path) -> None:
    s = z3.String("s")
    rel = _rel("inv", z3.StringSort())
    variables = {rel: (s,)}
    p = _write(
        tmp_path,
        """\
        (define-fun inv ((s String)) Bool
          (and (<= (str.len s) 8) (str.contains s "x")))
        """,
    )
    result = parse_candidate_file(p, variables)
    sexprs = _sexprs(result[rel])
    assert z3.simplify(z3.Length(s) <= 8).sexpr() in sexprs
    assert z3.simplify(z3.Contains(s, z3.StringVal("x"))).sexpr() in sexprs


# ---------------------------------------------------------------------------
# parse_candidate_file -- Real + String combination
# ---------------------------------------------------------------------------


def test_parse_candidate_file_binds_mixed_real_string_parameters(
    tmp_path: Path,
) -> None:
    total = z3.Real("total")
    log = z3.String("log")
    rel = _rel("inv", z3.RealSort(), z3.StringSort())
    variables = {rel: (total, log)}
    p = _write(
        tmp_path,
        """\
        (define-fun inv ((total Real) (log String)) Bool
          (= total (to_real (str.len log))))
        """,
    )
    result = parse_candidate_file(p, variables)
    assert len(result[rel]) == 1
    expected = z3.simplify(total == z3.ToReal(z3.Length(log)))
    assert result[rel][0].sexpr() == expected.sexpr()


# ---------------------------------------------------------------------------
# --cands / --dump-cands round trips (CLI level)
# ---------------------------------------------------------------------------


def test_real_round_trip_reproduces_success(tmp_path: Path, capsys) -> None:
    dump_path = tmp_path / "dumped.smt2"
    chc_file = str(REAL / "counter_safe.smt2")
    cands_file = str(CANDS / "real_counter_safe_candidates.smt2")

    rc1 = main(
        ["--cands", cands_file, "--dump-cands", str(dump_path), "--json", chc_file]
    )
    payload1 = json.loads(capsys.readouterr().out)
    assert rc1 == 0
    assert payload1["status"] == "success"
    # The weak `x = 0.0` candidate was dropped; only the correct one survives.
    assert payload1["houdini"]["candidates_removed"] == 1
    assert dump_path.exists()
    dumped_text = dump_path.read_text(encoding="utf-8")
    assert "Real" in dumped_text
    assert "10.0" in dumped_text

    rc2 = main(["--cands", str(dump_path), "--json", chc_file])
    payload2 = json.loads(capsys.readouterr().out)
    assert rc2 == 0
    assert payload2["status"] == "success"
    # Nothing left to drop: the dumped file already only has the invariant.
    assert payload2["houdini"]["candidates_removed"] == 0


def test_string_round_trip_reproduces_success(tmp_path: Path, capsys) -> None:
    dump_path = tmp_path / "dumped.smt2"
    chc_file = str(STRINGS / "bounded_append_safe.smt2")
    cands_file = str(CANDS / "string_bounded_append_candidates.smt2")

    rc1 = main(
        ["--cands", cands_file, "--dump-cands", str(dump_path), "--json", chc_file]
    )
    payload1 = json.loads(capsys.readouterr().out)
    assert rc1 == 0
    assert payload1["status"] == "success"
    assert payload1["houdini"]["candidates_removed"] == 1
    dumped_text = dump_path.read_text(encoding="utf-8")
    assert "String" in dumped_text
    assert "str.len" in dumped_text

    rc2 = main(["--cands", str(dump_path), "--json", chc_file])
    payload2 = json.loads(capsys.readouterr().out)
    assert rc2 == 0
    assert payload2["status"] == "success"
    assert payload2["houdini"]["candidates_removed"] == 0


def test_real_string_combination_round_trip_reproduces_success(
    tmp_path: Path, capsys
) -> None:
    dump_path = tmp_path / "dumped.smt2"
    chc_file = str(MIXED / "real_string_safe.smt2")
    cands_file = str(CANDS / "real_string_candidates.smt2")

    rc1 = main(
        ["--cands", cands_file, "--dump-cands", str(dump_path), "--json", chc_file]
    )
    payload1 = json.loads(capsys.readouterr().out)
    assert rc1 == 0
    assert payload1["status"] == "success"
    assert payload1["houdini"]["candidates_removed"] == 1
    dumped_text = dump_path.read_text(encoding="utf-8")
    assert "Real" in dumped_text
    assert "String" in dumped_text

    rc2 = main(["--cands", str(dump_path), "--json", chc_file])
    payload2 = json.loads(capsys.readouterr().out)
    assert rc2 == 0
    assert payload2["status"] == "success"
    assert payload2["houdini"]["candidates_removed"] == 0


def test_int_real_string_combination_round_trip_reproduces_success(
    tmp_path: Path, capsys
) -> None:
    dump_path = tmp_path / "dumped.smt2"
    chc_file = str(MIXED / "int_real_string_safe.smt2")
    cands_file = str(CANDS / "int_real_string_candidates.smt2")

    rc1 = main(
        ["--cands", cands_file, "--dump-cands", str(dump_path), "--json", chc_file]
    )
    payload1 = json.loads(capsys.readouterr().out)
    assert rc1 == 0
    assert payload1["status"] == "success"
    assert payload1["houdini"]["candidates_removed"] == 1

    rc2 = main(["--cands", str(dump_path), "--json", chc_file])
    payload2 = json.loads(capsys.readouterr().out)
    assert rc2 == 0
    assert payload2["status"] == "success"
    assert payload2["houdini"]["candidates_removed"] == 0
