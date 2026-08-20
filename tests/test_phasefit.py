"""Basic tests for PhaseFit branching-loop synthesis."""

from __future__ import annotations

from pathlib import Path

import z3

from pyhorn_bnd.horn import parse_chc_file
from pyhorn_bnd.phasefit import (
    extract_guarded_branches,
    compute_closed_form,
    run_phasefit,
    PhaseFit,
)
from pyhorn_bnd.seedminer import SeedMiner

EXAMPLES = Path(__file__).resolve().parents[1] / "examples" / "bench_horn"


def test_extract_branches_mixed_ite():
    prog = parse_chc_file(EXAMPLES / "03_mixed_bool_int_mod_ite.smt2")
    rule = next(r for r in prog.rules if r.is_inductive)
    branches = extract_guarded_branches(rule)
    assert len(branches) >= 2
    # Every update must be ite-free
    for b in branches:
        for u in b.updates.values():
            assert not (z3.is_app(u) and u.decl().kind() == z3.Z3_OP_ITE), (
                f"update still contains ite: {u}"
            )


def test_closed_form_increment():
    x = z3.Int("x")
    upd = x + 1
    cf = compute_closed_form(upd, x, [x])
    assert cf is not None
    n = __import__("sympy").Symbol("n", integer=True, nonnegative=True)
    # should be x0 + n
    assert n in cf.expr.free_symbols


def test_phasefit_runs_without_error():
    prog = parse_chc_file(EXAMPLES / "03_mixed_bool_int_mod_ite.smt2")
    results, cmap = run_phasefit(prog)
    assert len(results) == 1
    assert results[0].relation.name() == "inv"
    # candidates exist (at least seed atoms)
    assert results[0].relation in cmap
    assert len(cmap[results[0].relation]) >= 1


def test_phasefit_candidates_use_canonical_vars():
    prog = parse_chc_file(EXAMPLES / "03_mixed_bool_int_mod_ite.smt2")
    miner = SeedMiner(prog)
    seed = miner.mine()
    results, cmap = run_phasefit(prog, seed_result=seed)
    rel = results[0].relation
    canonical_ids = {v.get_id() for v in seed.variables[rel]}
    for cand in cmap[rel]:
        free = z3.z3util.get_vars(cand)
        for v in free:
            # every free var should be a canonical one (or a constant)
            if z3.is_const(v) and v.decl().kind() == z3.Z3_OP_UNINTERPRETED:
                assert v.get_id() in canonical_ids, f"foreign var {v} in {cand}"


def test_case_a_split_threshold_success(tmp_path):
    """Design Case A: y stays constant until x crosses 5000, then tracks x.

    PhaseFit + MultiHoudini should prove safety.
    """
    from pyhorn_bnd.houdini import MultiHoudini, HoudiniStatus
    from pyhorn_bnd.cands import merge_candidate_maps

    smt = tmp_path / "s_split_01_like.smt2"
    smt.write_text(
        """
(set-logic HORN)
(declare-fun inv (Int Int) Bool)
(assert (forall ((x Int) (y Int)) (=> (and (= x 0) (= y 5000)) (inv x y))))
(assert (forall ((x0 Int) (y0 Int) (x1 Int) (y1 Int))
  (=> (and (inv x0 y0)
           (= x1 (+ x0 1))
           (= y1 (ite (>= x0 5000) (+ y0 1) y0)))
      (inv x1 y1))))
(assert (forall ((x Int) (y Int))
  (=> (and (inv x y) (>= x 10000) (not (>= y 5000))) false)))
(check-sat)
"""
    )
    prog = parse_chc_file(smt)
    miner = SeedMiner(prog)
    seed = miner.mine()
    results, cmap = run_phasefit(prog, seed_result=seed)
    assert results and results[0].success
    # Must emit the characteristic phase lemmas (guarded).
    sexprs = " ".join(c.sexpr() for c in cmap[results[0].relation])
    assert "5000" in sexprs

    candidates = merge_candidate_maps(seed.candidates, cmap)
    houdini = MultiHoudini(prog, miner.variables, timeout_ms=3000)
    result = houdini.run(candidates, seed_result=seed)
    assert result.status == HoudiniStatus.SUCCESS


def test_mbp_branches_on_threshold():
    """MBP should recover the two complementary guards of a simple ite update."""
    from pyhorn_bnd.phasefit import extract_mbp_guarded_branches
    import tempfile, textwrap
    from pathlib import Path

    smt = Path("/tmp/mbp_threshold.smt2")
    smt.write_text(
        textwrap.dedent(
            """
            (set-logic HORN)
            (declare-fun inv (Int Int) Bool)
            (assert (forall ((x Int) (y Int)) (=> (= x 0) (inv x y))))
            (assert (forall ((x0 Int) (y0 Int) (x1 Int) (y1 Int))
              (=> (and (inv x0 y0)
                       (= x1 (+ x0 1))
                       (= y1 (ite (>= x0 10) (+ y0 1) y0)))
                  (inv x1 y1))))
            (assert (forall ((x Int) (y Int))
              (=> (and (inv x y) (>= x 100) (not (>= y 0))) false)))
            (check-sat)
            """
        )
    )
    prog = parse_chc_file(smt)
    rule = next(r for r in prog.rules if r.is_inductive)
    branches = extract_mbp_guarded_branches(rule)
    assert len(branches) == 2
    guards = {b.guard.sexpr() for b in branches}
    assert any("10" in g for g in guards)


def test_concretize_sympy_does_not_cross_bind_variables():
    """Regression test: _concretize_sympy used to match a sympy init symbol
    against init_state via a loose heuristic (any symbol name ending in
    "_0", which is *every* init symbol compute_closed_form produces) that
    ignored which Z3 variable the symbol was actually for. Whichever
    variable happened to be iterated first in init_state would "steal"
    the binding for every other variable's init symbol too, silently
    substituting the wrong concrete value into a boundary/candidate
    expression that doesn't even mention that variable.
    """
    import sympy as sp

    from pyhorn_bnd.phasefit import _concretize_sympy

    x = z3.Int("x")
    y = z3.Int("y")
    y0_sym = sp.Symbol("y_0", integer=True)
    # This expression references ONLY y's init symbol.
    expr = sp.Integer(5000) - y0_sym
    # x is first in iteration order but is NOT the variable this
    # expression is about.
    init_state = {x: z3.IntVal(0), y: z3.IntVal(999)}

    result = _concretize_sympy(expr, init_state, init_map=None)
    assert result == 4001, (
        f"expected 5000 - 999 = 4001, got {result} "
        "(4001 with x's value 0 substituted instead of y's 999 would "
        "indicate the cross-binding bug is back)"
    )


def test_concretize_sympy_three_variable_case_a_produces_correct_candidates():
    """End-to-end regression test for the same bug: an unrelated leading
    variable ('a', concrete value 999) in a 3-argument relation used to
    corrupt the classic Case A candidates -- "x == y" (once x crosses the
    threshold) became the objectively false "x == y - 4001" (999 leaking
    in via 5000 - 999 = 4001), and a bogus "x >= 5999" bound appeared.

    Note: "a == y - 4001" is a *separate*, legitimately true fact here
    (a=999 and y=5000 really do differ by 4001) and may legitimately
    appear as the consequent of a guarded lemma whose *antecedent*
    happens to mention x too -- so this test inspects each candidate's
    own free variables and, for implications, its consequent's free
    variables specifically, rather than substring-matching the whole
    printed formula.
    """
    smt = EXAMPLES.parent / "phasefit_regressions" / "case_a_3var.smt2"
    prog = parse_chc_file(smt)
    miner = SeedMiner(prog)
    seed = miner.mine()
    results, cmap = run_phasefit(prog, seed_result=seed)
    assert results and results[0].success

    canonical = miner.variables[results[0].relation]
    a, x, y = canonical[0], canonical[1], canonical[2]

    found_correct_xy_equality = False
    for c in cmap[results[0].relation]:
        core = c.arg(1) if z3.is_implies(c) else c
        try:
            free_ids = {v.get_id() for v in z3.z3util.get_vars(core)}
        except z3.Z3Exception:
            continue
        if free_ids != {x.get_id(), y.get_id()}:
            continue
        # This candidate relates exactly x and y (no a). It must not be
        # the corrupted "x == y - 4001"; a plain "x == y" is what we're
        # looking for.
        if z3.is_eq(core):
            solver = z3.Solver()
            solver.add(core != (x == y))
            if solver.check() == z3.unsat:
                found_correct_xy_equality = True
            solver2 = z3.Solver()
            solver2.add(core, x != y)
            assert solver2.check() == z3.unsat, (
                f"candidate {core} relating only x and y is not x == y "
                "-- looks like the corrupted-constant bug"
            )
    assert found_correct_xy_equality, "expected a plain x == y candidate"


def test_assemble_candidates_does_not_mutate_phase_init_state():
    """Regression test: assemble_candidates used to alias phase_init to
    ph.init_state directly (phase_init = ph.init_state or {}), then call
    phase_init.setdefault(...) with entries from global_init -- silently
    mutating the Phase object's own init_state as a side effect of what
    should have been a read-only merge.
    """
    from pyhorn_bnd.phasefit import Branch, ClosedForm, Phase, assemble_candidates

    x = z3.Int("x")
    y = z3.Int("y")
    branch = Branch(guard=z3.BoolVal(True), updates={x: x})
    original_init_state = {x: z3.IntVal(1)}
    ph = Phase(
        index=0,
        branch=branch,
        start_n=0,
        end_n=None,
        closed_forms={},
        init_state=original_init_state,
    )
    assemble_candidates([ph], [x, y], global_init={y: z3.IntVal(2)})
    assert ph.init_state == original_init_state, (
        f"ph.init_state was mutated: {ph.init_state}"
    )
    assert y not in ph.init_state
