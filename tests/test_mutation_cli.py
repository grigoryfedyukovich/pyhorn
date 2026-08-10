"""CLI-level tests for ``--mut``.

The heavy correctness burden lives in ``tests/test_mutation.py``, which
checks :func:`mutate_candidates` directly against hand-derived expected
output -- that's fully verifiable without a live solver. This file only
checks the CLI plumbing: the flag is validated the same way
``--validate-candidates`` is, it doesn't break an already-working example,
and end to end it visibly adds the expected candidate to the pool.

See ``examples/seed_houdini/transitive_bounds_safe.smt2`` and
``examples/cands/transitive_bounds_candidates.smt2``'s headers for why this
doesn't (and isn't trying to) demonstrate --mut being *necessary* for a
proof: Z3's own linear-arithmetic reasoning already combines simultaneously
-retained x<=y and y<=z hypotheses for free at certification time. What's
checked here is that --mut mechanically works: the derived x<=z candidate
shows up as a first-class member of the retained pool, not just an
implicit consequence the solver happens to notice.
"""

from __future__ import annotations

import json
from pathlib import Path

import pytest

from pyhorn_bnd.cli import main

ROOT = Path(__file__).resolve().parents[1]
SEED_HOUDINI = ROOT / "examples" / "seed_houdini"
CANDS = ROOT / "examples" / "cands"


# ---------------------------------------------------------------------------
# Validation / usage errors
# ---------------------------------------------------------------------------


def test_mut_without_houdini_mode_is_a_usage_error(capsys) -> None:
    with pytest.raises(SystemExit) as exc_info:
        main(["--mut", str(SEED_HOUDINI / "counter_safe.smt2")])
    assert exc_info.value.code == 2
    assert "--mut requires" in capsys.readouterr().err


# ---------------------------------------------------------------------------
# Regression: --mut must not break an already-working example
# ---------------------------------------------------------------------------


def test_mut_does_not_break_an_existing_success(capsys) -> None:
    rc = main(
        [
            "--seed-houdini",
            "--mut",
            str(SEED_HOUDINI / "counter_safe.smt2"),
        ]
    )
    out, _ = capsys.readouterr()
    assert rc == 0
    assert out.strip().splitlines()[-1] == "Success"


# ---------------------------------------------------------------------------
# End to end: --mut visibly adds the derived candidate to the pool
# ---------------------------------------------------------------------------


def test_mut_derives_transitive_bound_and_reaches_success(capsys) -> None:
    rc = main(
        [
            "--cands",
            str(CANDS / "transitive_bounds_candidates.smt2"),
            "--mut",
            "--json",
            str(SEED_HOUDINI / "transitive_bounds_safe.smt2"),
        ]
    )
    payload = json.loads(capsys.readouterr().out)
    assert rc == 0
    assert payload["status"] == "success"

    mutation = payload["mutation"]
    assert mutation is not None
    assert mutation["inequalities_considered"] == 2
    assert mutation["inequality_chains_combined"] == 1
    assert mutation["candidates_added"] == 1

    # The derived x<=z (positionally __inv_0 <= __inv_2 for a 3-arg
    # relation) should appear as a retained invariant in its own right.
    invariants = payload["invariants"]["inv"]
    assert any(
        "__inv_0" in inv and "__inv_2" in inv and inv.startswith("(<=")
        for inv in invariants
    )


def test_mut_debug_output_reports_statistics(capsys) -> None:
    rc = main(
        [
            "--cands",
            str(CANDS / "transitive_bounds_candidates.smt2"),
            "--mut",
            "--debug",
            str(SEED_HOUDINI / "transitive_bounds_safe.smt2"),
        ]
    )
    out, _ = capsys.readouterr()
    assert rc == 0
    assert "Mutation: equalities=0, inequalities=2, eq-pairs=0, " in out
    assert "ineq-chains=1, added=1" in out
