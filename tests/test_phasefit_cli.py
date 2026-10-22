"""CLI-level regression test for ``--phasefit`` run without ``--seed-houdini``.

A prior revision of the ``--phasefit`` branch in ``cli.py`` dropped the
merge of freshly-mined seed candidates into the working candidate pool
when ``--seed-houdini`` wasn't also given (it still *mined* them, for
PhaseFit's own atom-harvesting needs, but never folded the result back
into ``candidates``). Relations PhaseFit doesn't touch or can't split
were then left with zero candidates from a ``--phasefit``-only run,
silently contradicting ``--phasefit``'s own help text and turning a
provable "success" into "unknown" with no invariants at all -- entirely
unrelated to whatever else was being changed at the time, and not
caught by any existing test, since nothing exercised this exact flag
combination end to end. This test locks in the fix.
"""

from __future__ import annotations

import json
from pathlib import Path

from pyhorn_bnd.cli import main

ROOT = Path(__file__).resolve().parents[1]
SEED_HOUDINI = ROOT / "examples" / "seed_houdini"


def test_phasefit_only_still_merges_mined_seed_candidates(capsys) -> None:
    """``--phasefit`` alone (no ``--seed-houdini``) must still get the
    benefit of the seed candidates PhaseFit's own atom harvesting mines
    on its behalf -- not just PhaseFit's own generated candidates. On
    this example, dropping that merge is the difference between a
    genuine "success" proof and "unknown" with no invariants at all.
    """
    exit_code = main(
        [
            "--phasefit",
            "--json",
            str(SEED_HOUDINI / "multiple_predicates.smt2"),
        ]
    )
    out = json.loads(capsys.readouterr().out)
    assert exit_code == 0
    assert out["status"] == "success"
    assert out["invariants"]["p"]
    assert out["invariants"]["q"]


def test_phasefit_only_matches_phasefit_plus_seed_houdini(capsys) -> None:
    """A ``--phasefit``-only run should reach the same verdict as
    ``--phasefit --seed-houdini`` together on an example where nothing
    about the seed-mined candidates is specific to being *additionally*
    combined with an explicit ``--seed-houdini`` pass -- confirming the
    fresh-mine-and-merge path (taken when ``--seed-houdini`` is absent)
    isn't silently weaker than the already-merged path.
    """
    main(
        [
            "--phasefit",
            "--json",
            str(SEED_HOUDINI / "multiple_predicates.smt2"),
        ]
    )
    phasefit_only = json.loads(capsys.readouterr().out)

    main(
        [
            "--phasefit",
            "--seed-houdini",
            "--json",
            str(SEED_HOUDINI / "multiple_predicates.smt2"),
        ]
    )
    phasefit_and_seed = json.loads(capsys.readouterr().out)

    assert phasefit_only["status"] == phasefit_and_seed["status"] == "success"
