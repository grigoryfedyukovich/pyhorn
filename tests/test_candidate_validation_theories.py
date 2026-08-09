"""CLI-level candidate-validation coverage for Real, String, and mixed
theories.

``tests/test_candidate_validation.py`` and ``tests/test_candidate_validation_cli.py``
exercise ``--validate-candidates`` / ``--dump-promising-candidates`` / ``--cands``
thoroughly, but exclusively over Int examples from ``examples/seed_houdini/``.
``tests/test_real_arithmetic.py`` and ``tests/test_string_theory.py``
exercise Real and String thoroughly for parsing, the bounded explorer, and
SeedMiner/MultiHoudini (via ``--seed-houdini``), but never touch ``--cands``
or ``--validate-candidates``.

This file closes that gap: each example below pairs a genuinely too-tight
(or genuinely under-correlated) hand-picked candidate with a
``--cands`` file, so there is always something real for MultiHoudini to
drop and for ``--validate-candidates`` to classify -- mirroring the two
patterns already covered for Int in ``tests/test_candidate_validation_cli.py``:

- "confirmed real": ``real_counter_safe``, ``string_bounded_append``,
  ``real_string``, and ``int_real_string`` each supply one correct
  invariant plus one candidate that is true only at the initial fact, so
  it is dropped as soon as the very first transition step fires and is
  confirmed reachable at depth 2 (fact + one step).
- "potentially promising": ``real_helper_lemma`` and
  ``string_helper_lemma`` each supply a single, globally-true candidate
  that mentions only one of two correlated state components. Houdini's
  local induction check treats the other component as unconstrained and
  finds a counterexample-to-induction no real execution can reach, so
  bounded validation correctly reports it as promising rather than
  confirmed.

Note on ``--debug``: it writes a parse/mining/MultiHoudini summary to
*stdout* ahead of the final "Success"/"unknown" line, and writes the
per-removed-candidate "Dropped candidates" detail (including the
"confirmed real" / "potentially promising" verdict text asserted below) to
*stderr*. So stdout checks below look at the last line, not the whole
trimmed output.
"""

from __future__ import annotations

import json
from pathlib import Path

from pyhorn_bnd.cli import main

ROOT = Path(__file__).resolve().parents[1]
REAL = ROOT / "examples" / "real_arithmetic"
STRINGS = ROOT / "examples" / "string_theory"
MIXED = ROOT / "examples" / "mixed_theories"
CANDS = ROOT / "examples" / "cands"


def _last_line(out: str) -> str:
    return out.strip().splitlines()[-1]


# ---------------------------------------------------------------------------
# "Confirmed real" (reachable at depth 2) -- Real, String, and combinations
# ---------------------------------------------------------------------------


def test_real_counter_safe_confirmed_real_at_depth_2(capsys) -> None:
    rc = main(
        [
            "--cands",
            str(CANDS / "real_counter_safe_candidates.smt2"),
            "--validate-candidates",
            "--debug",
            str(REAL / "counter_safe.smt2"),
        ]
    )
    out, err = capsys.readouterr()
    assert rc == 0
    assert _last_line(out) == "Success"
    assert "check: confirmed real" in err
    assert "falsified by a reachable state at depth 2" in err


def test_real_counter_safe_json_witness_depth(capsys) -> None:
    rc = main(
        [
            "--cands",
            str(CANDS / "real_counter_safe_candidates.smt2"),
            "--validate-candidates",
            "--json",
            str(REAL / "counter_safe.smt2"),
        ]
    )
    assert rc == 0
    payload = json.loads(capsys.readouterr().out)
    entry = next(
        e for e in payload["removed_candidates"] if "0.0" in e["candidate"]
    )
    assert entry["candidate_validation"]["status"] == "reachable"
    assert entry["candidate_validation"]["witness_depth"] == 2


def test_string_bounded_append_confirmed_real_at_depth_2(capsys) -> None:
    rc = main(
        [
            "--cands",
            str(CANDS / "string_bounded_append_candidates.smt2"),
            "--validate-candidates",
            "--debug",
            str(STRINGS / "bounded_append_safe.smt2"),
        ]
    )
    out, err = capsys.readouterr()
    assert rc == 0
    assert _last_line(out) == "Success"
    assert "check: confirmed real" in err
    assert "falsified by a reachable state at depth 2" in err


def test_string_bounded_append_json_witness_depth(capsys) -> None:
    rc = main(
        [
            "--cands",
            str(CANDS / "string_bounded_append_candidates.smt2"),
            "--validate-candidates",
            "--json",
            str(STRINGS / "bounded_append_safe.smt2"),
        ]
    )
    assert rc == 0
    payload = json.loads(capsys.readouterr().out)
    entry = next(
        e for e in payload["removed_candidates"] if '""' in e["candidate"]
    )
    assert entry["candidate_validation"]["status"] == "reachable"
    assert entry["candidate_validation"]["witness_depth"] == 2


def test_real_string_combination_confirmed_real_at_depth_2(capsys) -> None:
    rc = main(
        [
            "--cands",
            str(CANDS / "real_string_candidates.smt2"),
            "--validate-candidates",
            "--debug",
            str(MIXED / "real_string_safe.smt2"),
        ]
    )
    out, err = capsys.readouterr()
    assert rc == 0
    assert _last_line(out) == "Success"
    assert "check: confirmed real" in err
    assert "falsified by a reachable state at depth 2" in err


def test_int_real_string_combination_confirmed_real_at_depth_2(capsys) -> None:
    rc = main(
        [
            "--cands",
            str(CANDS / "int_real_string_candidates.smt2"),
            "--validate-candidates",
            "--debug",
            str(MIXED / "int_real_string_safe.smt2"),
        ]
    )
    out, err = capsys.readouterr()
    assert rc == 0
    assert _last_line(out) == "Success"
    assert "check: confirmed real" in err
    assert "falsified by a reachable state at depth 2" in err


# ---------------------------------------------------------------------------
# "Potentially promising" (never found within the bound) -- Real and String
# ---------------------------------------------------------------------------


def test_real_helper_lemma_is_potentially_promising(capsys) -> None:
    rc = main(
        [
            "--cands",
            str(CANDS / "real_helper_lemma_candidates.smt2"),
            "--validate-candidates",
            "--debug",
            str(REAL / "helper_lemma_safe.smt2"),
        ]
    )
    out, err = capsys.readouterr()
    assert rc == 2  # the lone weak candidate does not prove the query safe
    assert _last_line(out) == "unknown"
    assert "potentially promising" in err
    assert "may need a helper lemma" in err


def test_string_helper_lemma_is_potentially_promising(capsys) -> None:
    rc = main(
        [
            "--cands",
            str(CANDS / "string_helper_lemma_candidates.smt2"),
            "--validate-candidates",
            "--debug",
            str(STRINGS / "helper_lemma_safe.smt2"),
        ]
    )
    out, err = capsys.readouterr()
    assert rc == 2
    assert _last_line(out) == "unknown"
    assert "potentially promising" in err
    assert "may need a helper lemma" in err


def test_real_helper_lemma_dump_promising_candidates_writes_real_sorts(
    tmp_path: Path,
) -> None:
    """--dump-promising-candidates' generated SMT-LIB2 file must declare the
    predicate with its real Real sort, not silently coerce it to Int. No
    String is involved here, so the file keeps `(set-logic HORN)` -- see
    the String version below for why that line is conditional."""
    out_dir = tmp_path / "cti_files"
    rc = main(
        [
            "--cands",
            str(CANDS / "real_helper_lemma_candidates.smt2"),
            "--validate-candidates",
            "--dump-promising-candidates",
            str(out_dir),
            str(REAL / "helper_lemma_safe.smt2"),
        ]
    )
    assert rc == 2
    files = list(out_dir.glob("*.smt2"))
    assert len(files) == 1
    content = files[0].read_text(encoding="utf-8")
    assert "(set-logic HORN)" in content
    assert "(declare-fun inv (Real Real) Bool)" in content
    assert "fail" not in content
    assert "(check-sat)" in content
    _assert_replays_in_z3(content)


def test_string_helper_lemma_dump_promising_candidates_writes_string_sorts(
    tmp_path: Path,
) -> None:
    """Same as above, for String: the dumped predicate signature must stay
    String, and the dumped rules must still carry native str.++ / str.substr
    terms rather than some Int-coerced approximation.

    Z3's own SMT-LIB2 parser rejects the String sort under an explicit
    `(set-logic HORN)` tag (confirmed by _assert_replays_in_z3 below raising
    "unknown sort 'String'" before this was fixed in
    render_candidate_verification_smt2), so unlike the Int and Real dumps,
    this file must NOT have that line -- otherwise the file this feature
    hands off to an external solver would fail to even parse there."""
    out_dir = tmp_path / "cti_files"
    rc = main(
        [
            "--cands",
            str(CANDS / "string_helper_lemma_candidates.smt2"),
            "--validate-candidates",
            "--dump-promising-candidates",
            str(out_dir),
            str(STRINGS / "helper_lemma_safe.smt2"),
        ]
    )
    assert rc == 2
    files = list(out_dir.glob("*.smt2"))
    assert len(files) == 1
    content = files[0].read_text(encoding="utf-8")
    assert "(set-logic HORN)" not in content
    assert "(declare-fun inv (String String) Bool)" in content
    assert "str.++" in content
    assert "str.substr" in content
    assert "fail" not in content
    assert "(check-sat)" in content
    _assert_replays_in_z3(content)


def _assert_replays_in_z3(smt2_text: str) -> None:
    """The dumped file must be independently loadable by Z3 (it is meant to
    be handed to any HORN-capable solver outside this tool)."""
    import z3

    z3.Solver().from_string(smt2_text)


# ---------------------------------------------------------------------------
# --cands as the escape hatch for a genuinely hard case
# ---------------------------------------------------------------------------


def test_cands_hand_derived_candidate_also_times_out(capsys) -> None:
    """This started out trying to demonstrate --cands succeeding where
    --seed-houdini cannot (SeedMiner genuinely can't synthesize a
    parity/modular invariant -- confirmed by
    tests/test_string_invariant_literature.py's
    test_syntactic_seedminer_does_not_overclaim_hard_regular_problems --
    but parity over a 2-symbol alphabet IS a regular property, so it's
    expressible as a regex; see
    examples/cands/coffee_can_odd_white_candidates.smt2 for the derivation,
    exhaustively checked against a brute-force reference independent of
    Z3: zero mismatches over every string of length 0-11 over {W, B}).

    That demonstration does not actually work in this environment, and
    this test records why rather than silently deleting the attempt.
    Run directly with --debug, the candidate parses correctly
    (`Cands: predicates=1, candidates=1`) and MultiHoudini never rejects
    it (`removed=0, remaining=1`) -- it times out mid-induction-check,
    before ever reaching certification, on rule r1 (`BB -> B`), which
    doesn't involve `W` at all and is content-irrelevant to this
    invariant. That rules out the regex itself as the cause: what's
    expensive is checking regex-membership invariance across an
    `x ++ OLD ++ y -> x ++ NEW ++ y` rewrite at an existentially-split
    position, for *any* regex, not something specific to this one or to
    `re.comp` (the earlier, different hard case in
    regex_alphabet_closure_safe.smt2). Every other documented hard case in
    docs/string_invariant_literature.md uses this same rewrite shape, so
    the same wall is expected there too -- not re-verified per-file here,
    since the mechanism is now understood and re-confirming it
    file-by-file wouldn't add information.

    So: correct candidate, still `unknown`. That's the right bar for a
    genuinely hard case like this one -- not finding a proof isn't a
    failure as long as it also doesn't claim a false Success or a false
    counterexample. The exact reason string Z3 reports for its internal
    timeout/cancellation is not asserted on: it's an incidental detail of
    this Z3 build, not something this tool controls or should be pinned
    to.
    """
    rc = main(
        [
            "--cands",
            str(CANDS / "coffee_can_odd_white_candidates.smt2"),
            "--debug",
            str(
                ROOT
                / "examples"
                / "string_invariant_literature"
                / "coffee_can_odd_white_safe.smt2"
            ),
        ]
    )
    out, _ = capsys.readouterr()
    assert rc == 2  # unknown -- not a false Success (0), not a false cex (1)
    assert out.strip().splitlines()[-1] == "unknown"
