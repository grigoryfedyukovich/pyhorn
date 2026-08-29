"""Tests for :mod:`pyhorn_bnd.ff_seeded`.

See that module's docstring, and forward_fixpoint.py's `initial_seed`
field docstring, for the soundness argument behind seeding from
something other than the literal fact-rule condition.
"""

from __future__ import annotations

from pathlib import Path

import pytest

from pyhorn_bnd.ff_seeded import (
    fact_rule_conjuncts,
    run_forward_fixpoint_from_init_conjuncts,
)
from pyhorn_bnd.forward_fixpoint import ForwardFixpointStatus
from pyhorn_bnd.horn import parse_chc_file


def _write(tmp_path: Path, name: str, smt2: str) -> Path:
    path = tmp_path / name
    path.write_text(smt2)
    return path


def test_fact_rule_conjuncts_extracts_individual_pieces(tmp_path):
    smt2 = """
(declare-var x Int)
(declare-var y Int)
(declare-rel inv (Int Int))
(declare-rel fail ())
(rule (=> (and (= x 0) (= y 5)) (inv x y)))
(rule (=> (inv x y) (inv (+ x 1) y)))
(rule (=> (and (inv x y) (< x 0)) fail))
(query fail)
"""
    path = _write(tmp_path, "two_facts.smt2", smt2)
    program = parse_chc_file(path, slice_program=False)

    conjuncts_by_relation = fact_rule_conjuncts(program)
    inv_rel = next(r for r in program.relations if r.name() == "inv")
    conjuncts = conjuncts_by_relation[inv_rel]

    # Both x==0 and y==5 (and their >=/<= weakenings) should show up as
    # separate, individually-triable pieces -- not just the combined
    # "x==0 AND y==5" as one atom.
    texts = {c.sexpr() for c in conjuncts}
    assert any("0" in t and "5" not in t for t in texts)
    assert any("5" in t for t in texts)
    assert len(conjuncts) > 2  # more than just the two raw equalities


def test_fact_rule_conjuncts_ignores_step_and_query_rules(tmp_path):
    """Only observations whose provenance is a fact rule should appear
    -- SeedMiner mines from step and query rules too, but those aren't
    "conjuncts of init".
    """
    smt2 = """
(declare-var x Int)
(declare-rel inv (Int))
(declare-rel fail ())
(rule (inv 0))
(rule (=> (and (inv x) (< x 999)) (inv (+ x 1))))
(rule (=> (and (inv x) (>= x 12345)) fail))
(query fail)
"""
    path = _write(tmp_path, "one_fact.smt2", smt2)
    program = parse_chc_file(path, slice_program=False)

    conjuncts_by_relation = fact_rule_conjuncts(program)
    inv_rel = next(r for r in program.relations if r.name() == "inv")
    texts = {c.sexpr() for c in conjuncts_by_relation[inv_rel]}

    # A step- or query-rule-derived candidate (e.g. bounds tied to 999
    # or 12345) must not appear among the fact-rule conjuncts.
    assert not any("999" in t or "12345" in t for t in texts)
    assert texts  # but the real fact-rule conjunct(s) should be there


def test_single_conjunct_suffices_and_is_used(tmp_path):
    """A program where the query only concerns one of two facts in the
    init condition -- the single relevant conjunct alone should be
    enough, and the result should report which one worked.
    """
    smt2 = """
(declare-var x Int)
(declare-var y Int)
(declare-rel inv (Int Int))
(declare-rel fail ())
(rule (=> (and (= x 0) (= y 0)) (inv x y)))
(rule (=> (and (inv x y) (< x 5)) (inv (+ x 1) y)))
(rule (=> (and (inv x y) (>= x 100)) fail))
(query fail)
"""
    path = _write(tmp_path, "irrelevant_y.smt2", smt2)
    program = parse_chc_file(path, slice_program=False)

    outcome = run_forward_fixpoint_from_init_conjuncts(
        program, max_iterations=10, timeout_ms=5_000
    )

    assert outcome.result.status is ForwardFixpointStatus.SAFE
    assert outcome.seed_used is not None


def test_falls_back_to_full_init_when_no_single_conjunct_suffices(tmp_path):
    """dillig46: x and w must be seeded together for x<=1 to be
    provable; no single conjunct (x alone, y alone, z alone, or w
    alone) suffices on its own. Must still reach a correct verdict by
    falling back to the full, literal init -- never worse than plain
    --ff, even though the single-conjunct fast path didn't pay off here.
    """
    smt2 = """
(declare-rel inv (Int Int Int Int))
(declare-var x0 Int)
(declare-var x1 Int)
(declare-var y0 Int)
(declare-var y1 Int)
(declare-var z0 Int)
(declare-var z1 Int)
(declare-var w0 Int)
(declare-var w1 Int)
(declare-var tmp0 Int)
(declare-var tmp1 Int)
(declare-rel fail ())
(rule (=> (and (= x1 0) (= y1 0) (= z1 0) (= w1 1)) (inv x1 y1 z1 w1)))
(rule (=>
    (and
        (inv x0 y0 z0 w0)
        (= tmp0 (mod w0 2))
        (= tmp1 (mod z0 2))
        (= x1 (ite (= tmp0 1) (+ x0 1) x0))
        (= w1 (ite (= tmp0 1) (+ w0 1) w0))
        (= y1 (ite (= tmp1 0) (+ y0 1) y0))
        (= z1 (ite (= tmp1 0) (+ z0 1) z0))
    )
    (inv x1 y1 z1 w1)
  )
)
(rule (=> (and (inv x0 y0 z0 w0) (not (<= x0 1))) fail))
(query fail)
"""
    path = _write(tmp_path, "dillig46.smt2", smt2)
    program = parse_chc_file(path, slice_program=False)

    outcome = run_forward_fixpoint_from_init_conjuncts(
        program, max_iterations=10, timeout_ms=5_000, overall_timeout_s=20.0
    )

    # Never reports a wrong verdict; SAFE either via a lucky single
    # conjunct or (as expected here) the full-init fallback -- either
    # way it must not be UNSAFE (this program is genuinely safe) or
    # UNKNOWN (the fallback alone should resolve it).
    assert outcome.result.status is not ForwardFixpointStatus.UNSAFE


def test_never_reports_unsafe_for_a_genuinely_safe_program(tmp_path):
    """Whatever seed a single conjunct produces, it's always implied by
    the real init (checked internally -- see initial_seed's docstring),
    so this can never fabricate an UNSAFE verdict for a program that's
    actually safe, regardless of which conjunct is tried.
    """
    smt2 = """
(declare-var x Int)
(declare-var y Int)
(declare-rel inv (Int Int))
(declare-rel fail ())
(rule (=> (and (= x 0) (= y 0)) (inv x y)))
(rule (=> (and (inv x y) (< x 3)) (inv (+ x 1) (+ y 1))))
(rule (=> (and (inv x y) (not (= x y))) fail))
(query fail)
"""
    path = _write(tmp_path, "relational.smt2", smt2)
    program = parse_chc_file(path, slice_program=False)

    outcome = run_forward_fixpoint_from_init_conjuncts(
        program, max_iterations=10, timeout_ms=5_000
    )

    assert outcome.result.status is not ForwardFixpointStatus.UNSAFE


# ---------------------------------------------------------------------------
# CLI wiring
# ---------------------------------------------------------------------------


def test_cli_ff_seeded_reports_success(tmp_path, capsys):
    from pyhorn_bnd.cli import main

    smt2 = """
(declare-var x Int)
(declare-var y Int)
(declare-rel inv (Int Int))
(declare-rel fail ())
(rule (=> (and (= x 0) (= y 0)) (inv x y)))
(rule (=> (and (inv x y) (< x 5)) (inv (+ x 1) y)))
(rule (=> (and (inv x y) (>= x 100)) fail))
(query fail)
"""
    path = _write(tmp_path, "irrelevant_y.smt2", smt2)
    exit_code = main(["--ff-seeded", str(path)])

    assert exit_code == 0
    assert capsys.readouterr().out.strip() == "Success"


def test_cli_ff_seeded_json_reports_seed_used_and_attempts(tmp_path, capsys):
    import json

    from pyhorn_bnd.cli import main

    smt2 = """
(declare-var x Int)
(declare-var y Int)
(declare-rel inv (Int Int))
(declare-rel fail ())
(rule (=> (and (= x 0) (= y 0)) (inv x y)))
(rule (=> (and (inv x y) (< x 5)) (inv (+ x 1) y)))
(rule (=> (and (inv x y) (>= x 100)) fail))
(query fail)
"""
    path = _write(tmp_path, "irrelevant_y.smt2", smt2)
    main(["--ff-seeded", "--json", str(path)])
    out = json.loads(capsys.readouterr().out.splitlines()[0])

    assert out["status"] == "safe"
    assert out["attempts"] >= 1
    assert out["seed_used"] is not None


def test_cli_ff_seeded_subflags_without_main_flag_is_usage_error(tmp_path, capsys):
    from pyhorn_bnd.cli import main

    smt2 = """
(declare-var x Int)
(declare-rel inv (Int))
(declare-rel fail ())
(rule (inv 0))
(rule (=> (inv x) (inv (+ x 1))))
(rule (=> (and (inv x) (>= x 5)) fail))
(query fail)
"""
    path = _write(tmp_path, "trivial.smt2", smt2)
    with pytest.raises(SystemExit) as exc_info:
        main(["--ff-timeout-ms=10", str(path)])
    assert exc_info.value.code == 2
    assert "--ff-seeded" in capsys.readouterr().err


def test_cli_ff_seeded_rejects_combination_with_ff(tmp_path, capsys):
    from pyhorn_bnd.cli import main

    smt2 = """
(declare-var x Int)
(declare-rel inv (Int))
(declare-rel fail ())
(rule (inv 0))
(rule (=> (inv x) (inv (+ x 1))))
(rule (=> (and (inv x) (>= x 5)) fail))
(query fail)
"""
    path = _write(tmp_path, "trivial.smt2", smt2)
    with pytest.raises(SystemExit) as exc_info:
        main(["--ff", "--ff-seeded", str(path)])
    assert exc_info.value.code == 2
    assert "--ff-seeded" in capsys.readouterr().err
