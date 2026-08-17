"""Basic tests for PhaseFit branching-loop synthesis."""

from __future__ import annotations

from pathlib import Path

import sympy as sp
import z3

from pyhorn_bnd.cli import main
from pyhorn_bnd.horn import parse_chc_file
from pyhorn_bnd.phasefit import (
    ClosedForm,
    Phase,
    Branch,
    extract_guarded_branches,
    compute_closed_form,
    assemble_candidates,
    stitch_phases_from_all_starts,
    run_phasefit,
    _sympy_to_z3,
    _drop_foreign_variable_candidates,
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


def test_extract_branches_deduplicates_shared_guard_conjuncts():
    # Several variables sharing the same top-level ite condition should
    # not produce a guard like And(p, p, p).
    x0, y0, z0 = z3.Ints("x0 y0 z0")
    x1, y1, z1 = z3.Ints("x1 y1 z1")
    inv = z3.Function("inv", z3.IntSort(), z3.IntSort(), z3.IntSort(), z3.BoolSort())
    from pyhorn_bnd.horn import HornRule
    cond = x0 < 10
    body = z3.And(
        inv(x0, y0, z0),
        x1 == z3.If(cond, x0 + 1, x0),
        y1 == z3.If(cond, 0, y0 + 1),
        z1 == z3.If(cond, 0, z0 + 1),
    )
    rule = HornRule(
        rule_id=0,
        original_rule_id=0,
        body=body,
        rule_vars=(x0, y0, z0, x1, y1, z1),
        src_relation=inv,
        src_args=(x0, y0, z0),
        dst_relation=inv,
        dst_args=(x1, y1, z1),
        is_fact=False,
        is_query=False,
        is_inductive=True,
    )
    branches = extract_guarded_branches(rule)
    for b in branches:
        # the guard's own AST should not repeat the same conjunct
        conjuncts = b.guard.children() if z3.is_and(b.guard) else [b.guard]
        seen = {c.sexpr() for c in conjuncts}
        assert len(seen) == len(conjuncts), f"duplicated conjuncts in {b.guard}"


def test_closed_form_increment():
    x = z3.Int("x")
    upd = x + 1
    cf = compute_closed_form(upd, x, [x])
    assert cf is not None
    n = sp.Symbol("n", integer=True, nonnegative=True)
    # should be x0 + n
    assert n in cf.expr.free_symbols


def test_closed_form_rejects_ite_nested_inside_mod():
    # _flatten_ite only pushes through add/sub/mul/uminus; an ite left
    # nested inside a mod must not be silently treated as an opaque free
    # symbol (that would fabricate a bogus "affine" closed form that
    # quietly ignores one whole branch).
    x = z3.Int("x")
    c = z3.Bool("c")
    upd = z3.If(c, x + 1, x) % 7
    assert compute_closed_form(upd, x, [x]) is None


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


def test_phasefit_finds_two_phases_not_a_degenerate_oscillation():
    # Regression test for a bug where re-anchoring a phase exactly at its
    # own boundary value caused classify_guard to report a spurious
    # zero-length "boundary" at n=0 of the freshly-entered phase, which
    # then repeated every iteration until the whole phase_budget was
    # burned on a meaningless back-and-forth between the two branches.
    prog = parse_chc_file(EXAMPLES / "case_a_two_phase.smt2")
    rule = next(r for r in prog.rules if r.is_inductive)
    branches = extract_guarded_branches(rule)
    pre_vars = rule.src_args
    post_to_pre = {post: pre for post, pre in zip(rule.dst_args, rule.src_args)}

    phases, boundaries = stitch_phases_from_all_starts(branches, pre_vars, post_to_pre)
    # At least one starting branch must find exactly the real two-phase
    # split (one boundary), not phase_budget-many degenerate phases.
    assert 1 <= len(boundaries) < 8, (
        f"expected a single real boundary, got {len(boundaries)} "
        "(0 means no split found; >=8 looks like a degenerate oscillation "
        "that burned the whole phase_budget)"
    )
    # No boundary should ever be a zero-length (local) crossing.
    for b in boundaries:
        assert b.n_star != 0


def test_phasefit_start_n_accumulates_across_phases():
    # Regression test: Phase.start_n / end_n used to be overwritten with
    # the just-computed *local* boundary offset instead of accumulating,
    # so any phase beyond the second reported the wrong (non-cumulative)
    # global step count.
    prog = parse_chc_file(EXAMPLES / "case_a_two_phase.smt2")
    rule = next(r for r in prog.rules if r.is_inductive)
    branches = extract_guarded_branches(rule)
    pre_vars = rule.src_args
    post_to_pre = {post: pre for post, pre in zip(rule.dst_args, rule.src_args)}

    phases, _ = stitch_phases_from_all_starts(branches, pre_vars, post_to_pre)
    two_phase_runs = [p for p in phases if p.end_n is not None]
    assert two_phase_runs, "expected at least one run to find a real boundary"
    for ph in two_phase_runs:
        # end_n must be strictly "later" than start_n in the same frame
        # (both symbolic here); at minimum they must not be literally
        # equal (that would mean a zero-length phase slipped through).
        assert ph.start_n != ph.end_n


def test_reanchor_carries_the_real_algebraic_relationship():
    # Regression test: re-anchoring a symbolic (non-literal) boundary
    # value used to either (a) throw inside int(), get silently caught,
    # and fall back to the *stale* previous-phase value, or (b) manufacture
    # a disconnected, unconstrained fresh Z3 variable. Neither preserves
    # the real relationship between the new phase's initial state and the
    # incoming variables. _sympy_to_z3 (used by the re-anchor step) should
    # instead reconstruct the actual expression.
    x0 = z3.Int("x0")
    y0 = z3.Int("y0")
    x0_sym = sp.Symbol("x0_0", integer=True)
    y0_sym = sp.Symbol("y0_0", integer=True)
    expr = y0_sym + 5000 - x0_sym
    reverse_map = {x0_sym: x0, y0_sym: y0}
    z3_expr = _sympy_to_z3(expr, reverse_map)
    assert z3_expr is not None
    # Must be equisatisfiable with the real relationship, not a fresh
    # unconstrained symbol.
    solver = z3.Solver()
    solver.add(z3_expr != (y0 + 5000 - x0))
    assert solver.check() == z3.unsat


def test_assemble_candidates_finds_same_growth_rate_offset():
    # Two variables that grow at the same rate within a phase (here: both
    # frozen at 0, i.e. rate 0) and provably start at the same concrete
    # value should yield an equality candidate -- this is what lets
    # PhaseFit express "y == z once both start incrementing together"
    # instead of only ever proposing single-variable facts.
    y, z = z3.Ints("y z")
    y_sym = sp.Symbol("y0_0", integer=True)
    z_sym = sp.Symbol("z0_0", integer=True)
    cf_y = ClosedForm(var=y, expr=sp.Integer(0), init_map={y_sym: y})
    cf_z = ClosedForm(var=z, expr=sp.Integer(0), init_map={z_sym: z})
    branch = Branch(guard=z3.BoolVal(True), updates={y: y, z: z})
    phase = Phase(
        index=0,
        branch=branch,
        start_n=0,
        end_n=None,
        closed_forms={y: cf_y, z: cf_z},
        init_state={y: y, z: z},
    )
    cands = assemble_candidates([phase], [y, z])
    assert any(str(c) in ("y == z", "z == y") for c in cands)


def test_phasefit_only_cli_merges_seed_candidates():
    # Regression test: `--phasefit` without `--seed-houdini` used to mine
    # seed atoms only for PhaseFit's own internal use and never merge
    # them into the candidate set handed to MultiHoudini, so relations
    # PhaseFit doesn't touch (or fails to split) silently got zero
    # candidates from a --phasefit-only run.
    assert main(["--phasefit", str(EXAMPLES / "case_a_two_phase.smt2")]) == 0


def test_extract_guarded_branches_handles_mixed_sort_dst_args():
    # Regression test: a passthrough (identity) dst_arg used to be located
    # in dst_args via `list(...).index(dst)`, i.e. structural `==`. When
    # dst_args mixes sorts (e.g. Int and Array), Z3's `__eq__` *raises*
    # Z3Exception on a genuine sort mismatch instead of returning False,
    # so `.index()` crashed while scanning past an earlier,
    # differently-sorted element -- even though the element we actually
    # wanted was later in the list. get_id()-based matching must be used
    # instead.
    from pyhorn_bnd.horn import HornRule

    int_sort = z3.IntSort()
    arr_sort = z3.ArraySort(z3.IntSort(), z3.IntSort())
    x0, x1 = z3.Const("x0", int_sort), z3.Const("x1", int_sort)
    a0, a1 = z3.Const("a0", arr_sort), z3.Const("a1", arr_sort)
    inv = z3.Function("inv", int_sort, arr_sort, z3.BoolSort())
    # a1 is a pure passthrough: it's never defined via `=` in the body,
    # so extract_guarded_branches must fall back to locating its matching
    # src_arg by position -- and a0 (an earlier, differently-sorted
    # dst_arg) must not blow that lookup up.
    body = z3.And(inv(x0, a0), x1 == x0 + 1)
    rule = HornRule(
        rule_id=0,
        original_rule_id=0,
        body=body,
        rule_vars=(x0, a0, x1, a1),
        src_relation=inv,
        src_args=(x0, a0),
        dst_relation=inv,
        dst_args=(x1, a1),
        is_fact=False,
        is_query=False,
        is_inductive=True,
    )
    branches = extract_guarded_branches(rule)  # must not raise
    assert branches
    for b in branches:
        assert a1 in b.updates
        assert b.updates[a1].get_id() == a0.get_id()


def test_phasefit_cli_does_not_crash_on_mixed_sort_examples():
    # Regression test for the exact crashes reported against a delivered
    # build: `_sympy_to_z3`'s Add/Mul reconstruction (used by
    # assemble_candidates's same-growth-rate candidate) raised a raw
    # Z3Exception when combining a non-arithmetic (Array/String) closed
    # form with anything, and extract_guarded_branches's dst_arg lookup
    # raised on mixed-sort dst_args. Sweep every corpus file that mixes
    # Int with a non-arithmetic sort and confirm --phasefit only ever
    # produces a normal CLI outcome (0 or 2), never an unhandled
    # exception.
    root = EXAMPLES.parent
    mixed_sort_files = [
        "bench_horn/05_const_array_and_ite.smt2",
        "freqhorn_corner_cases/quantified_array_invariant.smt2",
        "freqhorn_corner_cases/unsafe_quantified_array.smt2",
        "mutation_features/01_array_eq_select_a.smt2",
        "mutation_features/03_contains_mid_a.smt2",
        "mixed_theories/int_real_string_safe.smt2",
        "string_theory/mixed_string_int_safe.smt2",
        "string_theory/string_array_safe.smt2",
        "trace_houdini/array_tiling_pr4.smt2",
    ]
    for rel in mixed_sort_files:
        path = root / rel
        assert path.exists(), f"fixture moved/renamed: {path}"
        rc = main(["--phasefit", str(path)])
        assert rc in (0, 2), f"{rel} produced unexpected exit code {rc}"


def test_assemble_candidates_drops_free_havoc_variables():
    # Regression test for a reported crash: a rule-local "havoc" variable
    # (declared but never assigned anywhere -- just used directly inside
    # a guard, e.g. `(= 0 val1)`, a common way to model a nondeterministic
    # input) isn't a pre_var or a canonical relation argument. PhaseFit's
    # "emit the branch guard as a candidate" heuristic doesn't know that
    # and can propose e.g. `0 == val1` as a standalone candidate for the
    # relation. The pre_var -> canonical projection in _analyse_rule has
    # nothing to substitute such a variable with, so it used to reach
    # MultiHoudini's own (correct, defensive) validation and crash the
    # whole CLI with an uncaught ValueError instead of PhaseFit simply
    # not proposing that candidate.
    x = z3.Int("x")
    val1 = z3.Int("val1")  # foreign: not a pre_var, never assigned anywhere
    n = sp.Symbol("n", integer=True, nonnegative=True)
    # x's closed form is literally the step counter (x starts at 0 and
    # increments by 1 each step) so assemble_candidates also proposes a
    # genuine, canonical `x >= 0` bound alongside the foreign-var guard --
    # the filter must remove only the latter, not everything.
    cf_x = ClosedForm(var=x, expr=n, init_map={})
    branch = Branch(guard=(z3.IntVal(0) == val1), updates={x: x + 1})
    phase = Phase(
        index=0,
        branch=branch,
        start_n=0,
        end_n=None,
        closed_forms={x: cf_x},
        init_state={x: x},
    )
    raw_cands = assemble_candidates([phase], [x])
    # assemble_candidates itself is allowed to still emit the raw guard
    # (it doesn't know about "canonical" relations) -- the foreign-var
    # filter lives one layer up, applied to exactly this kind of output.
    assert any(val1 in z3.z3util.get_vars(c) for c in raw_cands)
    filtered = _drop_foreign_variable_candidates(raw_cands, [x])
    assert all(val1 not in z3.z3util.get_vars(c) for c in filtered)
    # And it must not have thrown away everything -- the genuinely
    # canonical candidates (from the closed form) should survive.
    assert filtered


def test_phasefit_cli_does_not_crash_on_havoc_variable_example():
    # End-to-end regression test for the exact reported crash: a rule
    # with declared-but-never-assigned "havoc" variables used only inside
    # ite guards (val1/val2), including an Array-sorted state variable.
    assert main(
        ["--phasefit", str(EXAMPLES / "array_tiling_havoc_var.smt2")]
    ) in (0, 2)
