"""Tests for forward reachability fixpoint computation via QE."""

from __future__ import annotations

import time
from pathlib import Path

import pytest
import z3

from pyhorn_bnd import forward_fixpoint as ff
from pyhorn_bnd.forward_fixpoint import (
    ForwardFixpoint,
    ForwardFixpointStatus,
    _contains_any_var,
    run_forward_fixpoint,
)
from pyhorn_bnd.horn import HornRule, parse_chc_file

ROOT = Path(__file__).resolve().parents[1]
STRING_EXAMPLES = ROOT / "examples" / "string_invariant_literature"
BENCH_EXAMPLES = ROOT / "examples" / "bench_horn"
FREQHORN_EXAMPLES = ROOT / "examples" / "freqhorn_corner_cases"


def _write(tmp_path: Path, name: str, smt2: str) -> Path:
    path = tmp_path / name
    path.write_text(smt2)
    return path


def test_bounded_loop_reaches_exact_fixpoint_and_is_safe(tmp_path):
    smt2 = """
(set-logic HORN)
(declare-fun inv (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (inv x))))
(assert (forall ((x0 Int) (x1 Int)) (=> (and (inv x0) (< x0 3) (= x1 (+ x0 1))) (inv x1))))
(assert (forall ((x Int)) (=> (and (inv x) (>= x 10)) false)))
(check-sat)
"""
    path = _write(tmp_path, "bounded_safe.smt2", smt2)
    program = parse_chc_file(path, slice_program=False)
    result = run_forward_fixpoint(program, max_iterations=10, timeout_ms=5000)
    assert result.status is ForwardFixpointStatus.SAFE
    assert result.fixpoint_reached
    relation = next(r for r in result.reached if r.name() == "inv")
    x = result.variables[relation][0]
    formula = result.reached[relation]
    # The exact reachable set is {0, 1, 2, 3}.
    solver = z3.Solver()
    solver.add(z3.Xor(formula, z3.And(x >= 0, x <= 3)))
    assert solver.check() == z3.unsat, formula


def test_violated_query_reports_unsafe_with_exact_counterexample(tmp_path):
    smt2 = """
(set-logic HORN)
(declare-fun inv (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (inv x))))
(assert (forall ((x0 Int) (x1 Int)) (=> (and (inv x0) (< x0 5) (= x1 (+ x0 1))) (inv x1))))
(assert (forall ((x Int)) (=> (and (inv x) (>= x 3)) false)))
(check-sat)
"""
    path = _write(tmp_path, "bounded_unsafe.smt2", smt2)
    program = parse_chc_file(path, slice_program=False)
    result = run_forward_fixpoint(program, max_iterations=10, timeout_ms=5000)
    assert result.status is ForwardFixpointStatus.UNSAFE
    assert result.violated_rule is not None
    assert result.counterexample_model is not None
    # The exact, minimal violating value is x == 3 -- confirm the reported
    # model actually says so (not just "found something").
    assert "3" in result.counterexample_model


def test_unbounded_loop_without_generalization_reports_unknown(tmp_path):
    # Same fixture as the generalization test below, but with
    # generalization explicitly disabled: reproduces the pre-widening
    # behavior for comparison -- an honest UNKNOWN, since the reachable
    # set never stabilizes within any finite number of naive Kleene steps.
    smt2 = """
(set-logic HORN)
(declare-fun inv (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (inv x))))
(assert (forall ((x0 Int) (x1 Int)) (=> (and (inv x0) (= x1 (+ x0 1))) (inv x1))))
(assert (forall ((x Int)) (=> (and (inv x) (< x 0)) false)))
(check-sat)
"""
    path = _write(tmp_path, "unbounded.smt2", smt2)
    program = parse_chc_file(path, slice_program=False)
    result = run_forward_fixpoint(
        program, max_iterations=5, timeout_ms=3000, enable_generalization=False
    )
    assert result.status is ForwardFixpointStatus.UNKNOWN
    assert not result.fixpoint_reached
    assert not result.generalized


def test_unbounded_loop_proven_safe_via_generalization(tmp_path):
    # Actually safe (x only ever increments from 0) and genuinely
    # unbounded -- the exact track alone never converges (previous test),
    # but interval widening should recognize the upper bound never
    # stabilizes and drop it, converging to the exact correct invariant
    # x >= 0 in a small, fixed number of rounds.
    smt2 = """
(set-logic HORN)
(declare-fun inv (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (inv x))))
(assert (forall ((x0 Int) (x1 Int)) (=> (and (inv x0) (= x1 (+ x0 1))) (inv x1))))
(assert (forall ((x Int)) (=> (and (inv x) (< x 0)) false)))
(check-sat)
"""
    path = _write(tmp_path, "unbounded.smt2", smt2)
    program = parse_chc_file(path, slice_program=False)
    result = run_forward_fixpoint(program, max_iterations=5, timeout_ms=3000)
    assert result.status is ForwardFixpointStatus.SAFE
    assert result.generalized
    relation = next(r for r in result.reached if r.name() == "inv")
    x = result.variables[relation][0]
    formula = result.reached[relation]
    solver = z3.Solver()
    solver.add(z3.Xor(formula, x >= 0))
    assert solver.check() == z3.unsat, formula


def test_widening_never_produces_a_false_unsafe_verdict(tmp_path):
    """Soundness-critical regression test: interval widening can and does
    introduce states that are not actually reachable (that's the entire
    point of over-approximation), so a query becoming satisfiable against
    the *generalized* track must never be reported as a genuine UNSAFE
    verdict -- only a hit against the exact track counts.

    Constructed so widening is forced to kick in and genuinely over-
    generalize: x is truly bounded to [0, 100], but with a small
    iteration budget the exact track cannot converge (~100 rounds would
    be needed), so its upper bound looks "still moving" every round and
    gets widened away to infinity. The query asks about x >= 1000 --
    unreachable in truth, but included in the widened (over-approximate)
    set. The correct, sound answer is UNKNOWN (can't prove safe, since
    the over-approximation does hit the query; must not claim unsafe,
    since the exact track never found a real violation).
    """
    smt2 = """
(set-logic HORN)
(declare-fun inv (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (inv x))))
(assert (forall ((x0 Int) (x1 Int)) (=> (and (inv x0) (< x0 100) (= x1 (+ x0 1))) (inv x1))))
(assert (forall ((x Int)) (=> (and (inv x) (>= x 1000)) false)))
(check-sat)
"""
    path = _write(tmp_path, "spurious.smt2", smt2)
    program = parse_chc_file(path, slice_program=False)
    result = run_forward_fixpoint(
        program, max_iterations=8, timeout_ms=2000, overall_timeout_s=15
    )
    assert result.status is not ForwardFixpointStatus.UNSAFE, (
        f"false UNSAFE from an over-approximation artifact: {result.message}"
    )


def test_interval_bounds_finds_tight_min_and_max():
    from pyhorn_bnd.forward_fixpoint import _interval_bounds

    x, y = z3.Ints("x y")
    formula = z3.And(x >= 2, x <= 7, y == 3)
    bounds = _interval_bounds(formula, (x, y), timeout_ms=2000)
    assert bounds is not None
    lo, hi = bounds[x.get_id()]
    assert lo is not None and lo.as_long() == 2
    assert hi is not None and hi.as_long() == 7
    ylo, yhi = bounds[y.get_id()]
    assert ylo is not None and ylo.as_long() == 3
    assert yhi is not None and yhi.as_long() == 3


def test_interval_bounds_reports_unbounded_as_none():
    from pyhorn_bnd.forward_fixpoint import _interval_bounds

    x = z3.Int("x")
    formula = x >= 5  # no upper bound
    bounds = _interval_bounds(formula, (x,), timeout_ms=2000)
    assert bounds is not None
    lo, hi = bounds[x.get_id()]
    assert lo is not None and lo.as_long() == 5
    assert hi is None


def test_widen_bounds_keeps_stable_and_drops_moving():
    from pyhorn_bnd.forward_fixpoint import _widen_bounds

    x, y = z3.Ints("x y")
    old = {x.get_id(): (z3.IntVal(0), z3.IntVal(3)), y.get_id(): (z3.IntVal(0), z3.IntVal(0))}
    new = {x.get_id(): (z3.IntVal(0), z3.IntVal(4)), y.get_id(): (z3.IntVal(0), z3.IntVal(0))}
    widened = _widen_bounds(old, new, (x, y))
    # x's lower bound was stable (0 == 0) -> kept; upper bound moved
    # (3 -> 4) -> widened away to unbounded (None).
    x_lo, x_hi = widened[x.get_id()]
    assert x_lo is not None and x_lo.as_long() == 0
    assert x_hi is None
    # y was fully stable on both sides -> both kept.
    y_lo, y_hi = widened[y.get_id()]
    assert y_lo is not None and y_lo.as_long() == 0
    assert y_hi is not None and y_hi.as_long() == 0


def test_bounds_to_formula_omits_unbounded_sides():
    from pyhorn_bnd.forward_fixpoint import _bounds_to_formula

    x = z3.Int("x")
    formula = _bounds_to_formula((x,), {x.get_id(): (z3.IntVal(2), None)})
    solver = z3.Solver()
    solver.add(z3.Xor(formula, x >= 2))
    assert solver.check() == z3.unsat, formula


def test_non_arithmetic_relation_is_unaffected_by_generalization(tmp_path):
    # A relation with a String argument can't be interval-widened -- must
    # fall back to the exact (unmodified) track entirely, same result as
    # with generalization disabled.
    smt2 = """
(set-logic HORN)
(declare-fun inv (String) Bool)
(assert (inv ""))
(assert (forall ((s0 String) (s1 String)) (=> (and (inv s0) (= s1 (str.++ s0 "a"))) (inv s1))))
(assert (forall ((s String)) (=> (and (inv s) (= s "aaa")) false)))
(check-sat)
"""
    path = _write(tmp_path, "string_loop.smt2", smt2)
    program = parse_chc_file(path, slice_program=False)
    with_gen = run_forward_fixpoint(program, max_iterations=6, timeout_ms=2000)
    without_gen = run_forward_fixpoint(
        program, max_iterations=6, timeout_ms=2000, enable_generalization=False
    )
    assert with_gen.status == without_gen.status
    assert not with_gen.generalized


def test_literal_fact_dst_args_do_not_produce_a_false_unsafe_verdict():
    """Regression test for a real bug: a fact rule's dst_args can be a
    literal constant rather than a plain variable (e.g. `(inv "MI")` with
    no rule-local variables at all -- exactly how a base-case string fact
    normalizes). The image-computation used to build the reachable-set
    formula by projecting onto dst_args and then *substituting* dst_args
    for the canonical variables afterward -- but substitution finds
    nothing to replace when dst_args is a literal that doesn't occur as a
    subterm of the projected formula, silently leaving the canonical
    variable totally unconstrained (i.e. "reachable for every possible
    value"), which can make an actually-safe query look satisfiable
    against the very first (over-broadened) reachable set.

    Reproduced directly against the real MU-puzzle benchmark, which is
    definitively SAFE (that's the entire point of the benchmark -- MU is
    unreachable from MI, the textbook count(I) mod 3 argument): the buggy
    version reported UNSAFE instantly (iteration 0, from the fact rule
    alone). This asserts the fixed behavior never regresses to that.
    """
    program = parse_chc_file(
        STRING_EXAMPLES / "hornstr_mu_puzzle_safe.smt2", slice_program=False
    )
    result = run_forward_fixpoint(
        program, max_iterations=2, timeout_ms=2000, overall_timeout_s=8
    )
    assert result.status is not ForwardFixpointStatus.UNSAFE, result.message
    # The specific failure mode was reporting UNSAFE at iteration 0 (i.e.
    # from the fact rule's own contribution, before any real forward step)
    assert not (result.iterations == 0 and result.violated_rule is not None)


def test_image_of_rule_ties_literal_dst_args_via_equality_not_substitution():
    """Direct unit test isolating the fix: a fact rule with dst_args that
    is a bare string literal (no rule-local variables) must produce a
    forward image asserting the canonical variable equals that literal --
    not an unconstrained True.
    """
    import time as _time

    from pyhorn_bnd.forward_fixpoint import ForwardFixpoint

    inv = z3.Function("inv", z3.StringSort(), z3.BoolSort())
    rule = HornRule(
        rule_id=0,
        original_rule_id=0,
        body=z3.BoolVal(True),
        rule_vars=(),
        src_relation=None,
        src_args=(),
        dst_relation=inv,
        dst_args=(z3.StringVal("MI"),),
        is_fact=True,
        is_query=False,
        is_inductive=False,
    )

    class _FakeProgram:
        relations = (inv,)
        rules = (rule,)

    ff = ForwardFixpoint(_FakeProgram(), max_iterations=1, timeout_ms=2000)
    image = ff._image_of_rule(rule, {}, tainted=set(), deadline=_time.monotonic() + 5)
    assert image is not None
    canonical = ff._resolved_variables[inv][0]
    solver = z3.Solver()
    solver.add(z3.Xor(image, canonical == z3.StringVal("MI")))
    assert solver.check() == z3.unsat, image


def test_full_corpus_never_crashes_and_never_reports_unsafe_for_known_safe():
    """Sweep a handful of the corpus's *known-safe* benchmarks (per their
    own manifest.json / bench_horn expectations elsewhere in this repo)
    and confirm forward_fixpoint never reports UNSAFE for any of them --
    it may (and often will, for anything beyond small bounded loops)
    report UNKNOWN, which is always a safe non-claim, but a definite
    UNSAFE verdict here is only ever correct when backed by an exact,
    sound forward-reachability counterexample, and must never happen for
    a genuinely safe program.
    """
    known_safe = [
        STRING_EXAMPLES / "hornstr_mu_puzzle_safe.smt2",
        STRING_EXAMPLES / "coffee_can_odd_white_safe.smt2",
        BENCH_EXAMPLES / "05_const_array_and_ite.smt2",
    ]
    for path in known_safe:
        assert path.exists(), f"fixture moved/renamed: {path}"
        program = parse_chc_file(path, slice_program=False)
        result = run_forward_fixpoint(
            program, max_iterations=4, timeout_ms=1500, overall_timeout_s=8
        )
        assert result.status is not ForwardFixpointStatus.UNSAFE, (
            f"{path.name}: false UNSAFE verdict -- {result.message}"
        )


def test_unresolvable_qe_never_produces_a_false_safe_verdict():
    """Soundness-critical regression test for a real bug: when QE cannot
    resolve a fact rule's own body (here: an array initialization
    invariant, `forall i. a[i] = i`, that Z3's "qe" tactic legitimately
    can't turn into a quantifier-free formula), the relation's reachable-
    set formula used to silently stay at its `False` ("nothing here yet")
    default -- and every later query check and fixpoint comparison read
    that `False` as *proof the relation is empty*, rather than *we
    couldn't determine what's reachable*. That is unsound: it reported
    `examples/freqhorn_corner_cases/unsafe_quantified_array.smt2` -- a
    program that is genuinely, deliberately unsafe -- as SAFE, instantly,
    because the one fact rule that seeds `inv1` failed to project and the
    algorithm treated "failed to compute" as "computed empty".

    The fix tracks which relations are *tainted* (their current formula
    is known-incomplete because some contributing computation failed) and
    propagates that transitively: a query check or fixpoint comparison
    involving a tainted relation is always undecided, never "definitely
    safe". The correct answer for this program at a small iteration
    budget is UNKNOWN -- neither the false SAFE this used to produce, nor
    (since the exact track only ever reports UNSAFE from a genuine,
    successfully-computed witness, which this program's own QE failure
    prevents) an over-eager UNSAFE either.
    """
    program = parse_chc_file(
        FREQHORN_EXAMPLES / "unsafe_quantified_array.smt2", slice_program=False
    )
    result = run_forward_fixpoint(
        program, max_iterations=6, timeout_ms=1200, overall_timeout_s=10
    )
    assert result.status is ForwardFixpointStatus.UNKNOWN, (
        f"expected honest UNKNOWN, got {result.status}: {result.message}"
    )


def test_has_quantifier_detects_leftover_quantifiers():
    from pyhorn_bnd.forward_fixpoint import _has_quantifier

    i = z3.Int("i")
    a = z3.Array("a", z3.IntSort(), z3.IntSort())
    quantified = z3.ForAll([i], a[i] == i)
    assert _has_quantifier(quantified)
    assert not _has_quantifier(z3.And(a[0] == 0, i > 0))


def test_qe_exists_rejects_a_result_with_a_leftover_quantifier():
    """Direct unit test for the fix: even when there are no rule-local
    variables to eliminate (the common shape of a simple fact rule), a
    body that already contains its own quantifier must not be passed
    through as if it were quantifier-free.
    """
    from pyhorn_bnd.forward_fixpoint import _qe_exists

    i = z3.Int("i")
    a = z3.Array("a", z3.IntSort(), z3.IntSort())
    body = z3.ForAll([i], a[i] == i)
    assert _qe_exists((), body, timeout_ms=2000) is None


def test_taint_propagates_and_blocks_a_premature_fixpoint():
    """Direct unit test isolating the taint-propagation mechanism itself,
    independent of the array/QE specifics that first surfaced it: a fact
    rule whose body cannot be resolved (quantified, unconditionally)
    taints its relation; a second relation that depends on the first
    must never reach a trusted "fixpoint" (SAFE) while that taint is
    unresolved, even though its own formula technically stops changing
    round to round (because nothing new can ever be derived from an
    always-None image).
    """
    i = z3.Int("i")
    a = z3.Array("a", z3.IntSort(), z3.IntSort())
    src = z3.Function("src", z3.ArraySort(z3.IntSort(), z3.IntSort()), z3.BoolSort())
    dst = z3.Function("dst", z3.IntSort(), z3.BoolSort())

    fact = HornRule(
        rule_id=0,
        original_rule_id=0,
        body=z3.ForAll([i], a[i] == i),  # cannot be QE'd away
        rule_vars=(),
        src_relation=None,
        src_args=(),
        dst_relation=src,
        dst_args=(a,),
        is_fact=True,
        is_query=False,
        is_inductive=False,
    )
    n0, n1 = z3.Ints("n0 n1")
    step = HornRule(
        rule_id=1,
        original_rule_id=1,
        body=(n1 == 0),
        rule_vars=(a, n0, n1),
        src_relation=src,
        src_args=(a,),
        dst_relation=dst,
        dst_args=(n1,),
        is_fact=False,
        is_query=False,
        is_inductive=True,
    )

    class _FakeProgram:
        relations = (src, dst)
        rules = (fact, step)

    result = run_forward_fixpoint(_FakeProgram(), max_iterations=4, timeout_ms=1500)
    assert result.status is ForwardFixpointStatus.UNKNOWN


# ---------------------------------------------------------------------------
# Regression: the QE free-variable-leak check must not be able to dominate
# runtime on a growing formula (see _contains_any_var's docstring).
# ---------------------------------------------------------------------------


def test_contains_any_var_matches_z3util_get_vars_semantics():
    """``_contains_any_var`` must agree with ``z3.z3util.get_vars`` on
    what counts as a free variable (an uninterpreted 0-arity constant) --
    it's a faster replacement for the same check, not a different one.
    """
    x, y = z3.Ints("x y")
    a = z3.Bool("a")
    formula = z3.And(x + y == 0, z3.Implies(a, y > 0), z3.IntVal(3) == 3)
    reference_ids = {v.get_id() for v in z3.z3util.get_vars(formula)}

    assert _contains_any_var(formula, {x.get_id()})
    assert _contains_any_var(formula, {y.get_id()})
    assert _contains_any_var(formula, {a.get_id()})
    assert not _contains_any_var(formula, {z3.Int("unrelated").get_id()})
    assert x.get_id() in reference_ids and y.get_id() in reference_ids
    assert a.get_id() in reference_ids


def test_growing_reachable_set_does_not_blow_up_wall_clock_time(tmp_path):
    """A relation whose reachable-set formula grows every round (the
    common, expected case for anything that doesn't converge quickly --
    see the module docstring's discussion of the generalized track) must
    not cause per-call wall-clock time to blow up independent of
    ``timeout_ms``. Before the fix, this exact shape (an unbounded
    counter with no early QE failure or convergence) took over 40s
    wall-clock for 15 rounds despite a 10ms per-call timeout budget --
    entirely dominated by ``z3.z3util.get_vars``, which has no timeout
    hook at all and scales very badly with formula size. With the fix,
    the same run completes in well under the CI-safe bound below.
    """
    smt2 = """
(set-logic HORN)
(declare-fun inv (Int Int Int) Bool)
(assert (forall ((x Int) (y Int) (len Int)) (=> (and (= x 0) (= y 0)) (inv x y len))))
(assert (forall ((x Int) (y Int) (len Int) (x1 Int) (y1 Int))
  (=> (and (inv x y len) (< x len) (= x1 (+ x 1)) (= y1 (+ y 2))) (inv x1 y1 len))))
(assert (forall ((x Int) (y Int) (len Int)) (=> (and (inv x y len) (not (= y (* 2 x)))) false)))
(check-sat)
"""
    path = _write(tmp_path, "growing_counter.smt2", smt2)
    program = parse_chc_file(path, slice_program=False)

    start = time.monotonic()
    result = run_forward_fixpoint(
        program,
        max_iterations=20,
        timeout_ms=10,
        overall_timeout_s=30.0,
        enable_generalization=False,
    )
    elapsed = time.monotonic() - start

    # Generous bound: the fixed version finishes in ~1s locally. 15s
    # leaves headroom for slow CI machines while still catching the
    # ~40s-and-growing blowup the unfixed get_vars-based check produced.
    assert elapsed < 15.0, (
        f"forward fixpoint took {elapsed:.1f}s for a growing-formula "
        "input that should stay fast regardless of timeout_ms -- likely "
        "a reintroduction of the unbounded z3util.get_vars leak check"
    )
    # This benchmark's true invariant (y == 2*x) is relational, so
    # neither the exact track (bounded by max_iterations) nor the
    # non-relational interval-widened track (which drops the x/y
    # correlation) can prove it here -- UNKNOWN is the honest, expected
    # verdict. The point of this test is the wall-clock bound above, not
    # the verdict itself.
    assert result.status is ForwardFixpointStatus.UNKNOWN


# ---------------------------------------------------------------------------
# CLI: the --ff-* tuning flags must require --ff itself, rather than
# silently doing nothing and falling through to the default bounded-explorer
# pipeline (which for a divergent/unbounded program can run far longer than
# any of the timeouts the person actually asked for -- this is exactly what
# happened before this check existed).
# ---------------------------------------------------------------------------


@pytest.mark.parametrize(
    "flag",
    [
        "--ff-max-iterations=5",
        "--ff-timeout-ms=10",
        "--ff-overall-timeout-s=5",
        "--ff-no-generalization",
        "--ff-widening-delay=1",
    ],
)
def test_forward_fixpoint_subflag_without_main_flag_is_a_usage_error(
    tmp_path, capsys, flag
):
    from pyhorn_bnd.cli import main

    smt2 = """
(set-logic HORN)
(declare-fun inv (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (inv x))))
(assert (forall ((x Int)) (=> (inv x) false)))
(check-sat)
"""
    path = _write(tmp_path, "trivial.smt2", smt2)
    with pytest.raises(SystemExit) as exc_info:
        main([flag, str(path)])
    assert exc_info.value.code == 2
    assert "require --ff" in capsys.readouterr().err


def test_forward_fixpoint_subflags_work_together_with_main_flag(tmp_path, capsys):
    from pyhorn_bnd.cli import main

    smt2 = """
(set-logic HORN)
(declare-fun inv (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (inv x))))
(assert (forall ((x0 Int) (x1 Int)) (=> (and (inv x0) (< x0 3) (= x1 (+ x0 1))) (inv x1))))
(assert (forall ((x Int)) (=> (and (inv x) (>= x 10)) false)))
(check-sat)
"""
    path = _write(tmp_path, "bounded_safe.smt2", smt2)
    exit_code = main(
        [
            "--ff",
            "--ff-no-generalization",
            "--ff-timeout-ms=10",
            str(path),
        ]
    )
    assert exit_code == 0
    assert capsys.readouterr().out.strip() == "Success"


# ---------------------------------------------------------------------------
# Regression: Z3's `qe` tactic is not always sound on formulas mixing
# integer `%` (mod) with `If`/ite -- it can return a result satisfied by a
# state with no real predecessor under the rule, even with a generous
# (60s) timeout, so this is not a timeout artifact. Confirmed on a real
# benchmark (dillig46): every exact-track query hit must now be
# independently re-checked via BoundedExplorer before being reported as
# UNSAFE (see the module docstring's CAUTION note and
# `_confirm_counterexample`).
# ---------------------------------------------------------------------------

_DILLIG46_SMT2 = """
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

(query fail :print-certificate true)
"""


def test_qe_over_approximation_on_dillig46_is_not_reported_as_unsafe(tmp_path):
    """The concrete regression this module shipped once: with a small
    per-call timeout, `qe` returns a leak-free but over-approximate
    image for this program's step rule, and a naive reading reports a
    fabricated counterexample (x0=2) for a program that is actually
    safe -- x can be shown, by direct concrete simulation, to freeze at
    1 forever once w becomes even. Confirmed independently via
    BoundedExplorer up to depth 10 (BOUNDED_SAFE) and via
    Seed-Houdini/Trace-Houdini (Success) in the original bug report.
    This must never come back as UNSAFE; UNKNOWN (or, if `qe` happens
    not to reproduce the bad result this run, SAFE) is acceptable --
    only UNSAFE is not. Whether the underlying `qe` misbehavior
    actually triggers on a given run has turned out to depend on prior
    Z3 context state within the process (see
    `test_confirm_counterexample_rejects_a_forced_over_approximation`
    for a deterministic, environment-independent test of the rejection
    mechanism itself); this test is a best-effort canary against a
    regression on the exact original benchmark, not a guaranteed
    trigger.
    """
    path = _write(tmp_path, "dillig46.smt2", _DILLIG46_SMT2)
    program = parse_chc_file(path, slice_program=False)

    result = run_forward_fixpoint(
        program, max_iterations=10, timeout_ms=100, overall_timeout_s=30.0
    )

    assert result.status is not ForwardFixpointStatus.UNSAFE


def test_confirm_counterexample_rejects_a_forced_over_approximation(
    tmp_path, monkeypatch
):
    """Deterministic, environment-independent test of the rejection
    mechanism itself (unlike the dillig46 canary above, which depends
    on `qe`'s own, apparently context-sensitive, misbehavior actually
    triggering): force `_qe_exists` to always return an unconditionally
    true (maximally over-approximate) image, on a program where the
    real reachable range of x is capped at 10 by the step rule's own
    guard but the query only fires at x>=100 -- x=100 is genuinely
    unreachable, confirmable by BoundedExplorer independent of the
    forced bad image. The forced over-approximation should make
    `reached` claim everything is reachable immediately, which would
    trigger a query hit on the very first round; the confirmation gate
    must catch and reject it rather than report UNSAFE.
    """
    smt2 = """
(declare-var x Int)
(declare-rel inv (Int))
(declare-rel fail ())
(rule (inv 0))
(rule (=> (and (inv x) (< x 10)) (inv (+ x 1))))
(rule (=> (and (inv x) (>= x 100)) fail))
(query fail)
"""
    path = _write(tmp_path, "capped_counter.smt2", smt2)
    program = parse_chc_file(path, slice_program=False)

    def forced_over_approximation(vars_to_eliminate, body, *, timeout_ms):
        return z3.BoolVal(True)

    monkeypatch.setattr(ff, "_qe_exists", forced_over_approximation)

    result = ff.run_forward_fixpoint(
        program, max_iterations=5, timeout_ms=1_000, overall_timeout_s=10.0
    )

    assert result.status is not ForwardFixpointStatus.UNSAFE
    assert result.qe_unsound_rejections >= 1


def test_confirm_counterexample_depth_is_sufficient(tmp_path):
    """`_confirm_counterexample`'s depth bound must account for
    BoundedExplorer counting the fact rule and the query rule as part
    of the trace length, not just the exact track's own step count --
    an earlier version passed the step count straight through as
    `upto` and, as a result, wrongly rejected this genuine
    counterexample (found after 2 exact-track rounds, but only
    confirmable by BoundedExplorer at trace length 4: fact + 2 steps +
    query) as unconfirmed, turning a real UNSAFE into a false UNKNOWN.
    """
    smt2 = """
(set-logic HORN)
(declare-var x Int)
(declare-rel inv (Int))
(declare-rel fail ())
(rule (inv 0))
(rule (=> (and (inv x) (< x 2)) (inv (+ x 1))))
(rule (=> (and (inv x) (>= x 2)) fail))
(query fail)
"""
    path = _write(tmp_path, "rule_syntax_unsafe.smt2", smt2)
    program = parse_chc_file(path, slice_program=False)

    result = run_forward_fixpoint(
        program, max_iterations=20, timeout_ms=10_000, overall_timeout_s=30.0
    )

    assert result.status is ForwardFixpointStatus.UNSAFE
    assert result.qe_unsound_rejections == 0


def test_genuinely_unsafe_program_still_reports_unsafe(tmp_path):
    """The confirmation gate must not make the exact track blind to
    real bugs -- it should only reject hits BoundedExplorer can't also
    find, never hits it can.
    """
    smt2 = """
(declare-var x Int)
(declare-rel inv (Int))
(declare-rel fail ())
(rule (inv 0))
(rule (=> (inv x) (inv (+ x 1))))
(rule (=> (and (inv x) (>= x 2)) fail))
(query fail)
"""
    path = _write(tmp_path, "counter_unsafe.smt2", smt2)
    program = parse_chc_file(path, slice_program=False)

    result = run_forward_fixpoint(program, max_iterations=10, timeout_ms=5_000)

    assert result.status is ForwardFixpointStatus.UNSAFE
    assert result.counterexample_model is not None


# ---------------------------------------------------------------------------
# initial_seed: seeding round 0 from a formula other than the literal
# fact-rule condition, provided Init implies it.
# ---------------------------------------------------------------------------


def test_initial_seed_that_drops_an_irrelevant_variable_still_proves_safe(
    tmp_path,
):
    """x and w are tied together (both freeze permanently the first
    round w's threshold condition goes false); y and z are a
    completely separate pair the query never touches, incrementing
    unconditionally every round regardless of anything else. Seeding
    with just (x==0 AND w==1) -- dropping y and z entirely, leaving
    them unconstrained -- should still prove x<=1, since x's own
    reachable range never depended on y or z at all. In fact the full,
    unseeded computation (all four variables, y and z included) does
    *not* reliably converge to this same proof -- confirmed
    reproducible over repeated runs -- which is itself a small,
    concrete demonstration of this module's value: variables that are
    genuinely irrelevant to a query can still make the full joint `qe`
    computation less able to find a proof it can find once they're
    dropped, not just slower.
    """
    smt2 = """
(declare-rel inv (Int Int Int Int))
(declare-var x0 Int)
(declare-var x1 Int)
(declare-var w0 Int)
(declare-var w1 Int)
(declare-var y0 Int)
(declare-var y1 Int)
(declare-var z0 Int)
(declare-var z1 Int)
(declare-rel fail ())
(rule (=> (and (= x1 0) (= w1 1) (= y1 0) (= z1 0)) (inv x1 y1 z1 w1)))
(rule (=>
    (and
        (inv x0 y0 z0 w0)
        (= x1 (ite (<= w0 1) (+ x0 1) x0))
        (= w1 (ite (<= w0 1) (+ w0 1) w0))
        (= y1 (+ y0 1))
        (= z1 (+ z0 1))
    )
    (inv x1 y1 z1 w1)
  )
)
(rule (=> (and (inv x0 y0 z0 w0) (not (<= x0 1))) fail))
(query fail)
"""
    path = _write(tmp_path, "threshold_pair.smt2", smt2)
    program = parse_chc_file(path, slice_program=False)
    inv_rel = next(r for r in program.relations if r.name() == "inv")
    canon = ForwardFixpoint(program)._resolved_variables[inv_rel]
    x, _y, _z, w = canon

    seed = z3.And(x == 0, w == 1)
    result = run_forward_fixpoint(
        program,
        max_iterations=10,
        timeout_ms=5_000,
        initial_seed={inv_rel: seed},
    )

    assert result.status is ForwardFixpointStatus.SAFE


def test_initial_seed_dropping_a_needed_variable_does_not_converge(tmp_path):
    """The flip side of the test above: x's own update depends on w's
    parity, so seeding with x==0 alone (w, y, z all left unconstrained)
    can't establish x<=1 the way (x==0 AND w==1) does above -- w's
    parity becomes arbitrary each round, so x looks able to grow
    forever. Must come back UNKNOWN, never a wrong verdict. (The
    reduced 2-variable version of this program, x and w only with no y
    or z, turns out to still converge to SAFE even with w dropped --
    w's own update happens to always land on an even value after one
    step regardless of where it started, a genuine mathematical fact
    about this particular arithmetic, not a bug. This test uses the
    full 4-variable program specifically because *that* one doesn't
    converge with x alone -- interesting on its own: extra, genuinely
    irrelevant variables (y, z) still in play made qe less able to
    find the SAFE proof here, not more.)
    """
    smt2 = _DILLIG46_SMT2
    path = _write(tmp_path, "dillig46.smt2", smt2)
    program = parse_chc_file(path, slice_program=False)
    inv_rel = next(r for r in program.relations if r.name() == "inv")
    canon = ForwardFixpoint(program)._resolved_variables[inv_rel]
    x, _y, _z, _w = canon

    result = run_forward_fixpoint(
        program,
        max_iterations=10,
        timeout_ms=5_000,
        initial_seed={inv_rel: x == 0},
    )

    assert result.status is ForwardFixpointStatus.UNKNOWN


def test_initial_seed_violating_init_raises(tmp_path):
    """A seed Init doesn't imply -- one that excludes a real initial
    state -- is not a sound basis for a proof about the real program,
    so this must fail loudly rather than silently substitute or ignore
    it.
    """
    smt2 = """
(declare-var x Int)
(declare-rel inv (Int))
(declare-rel fail ())
(rule (inv 0))
(rule (=> (inv x) (inv (+ x 1))))
(rule (=> (and (inv x) (>= x 100)) fail))
(query fail)
"""
    path = _write(tmp_path, "trivial.smt2", smt2)
    program = parse_chc_file(path, slice_program=False)
    inv_rel = next(r for r in program.relations if r.name() == "inv")
    canon = ForwardFixpoint(program)._resolved_variables[inv_rel]
    (x,) = canon

    with pytest.raises(ValueError, match="does not satisfy Init"):
        run_forward_fixpoint(
            program,
            max_iterations=5,
            timeout_ms=5_000,
            initial_seed={inv_rel: x == 5},
        )

