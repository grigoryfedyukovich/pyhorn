"""Tests for :mod:`pyhorn_bnd.ff_houdini`.

See that module's docstring for the design: gather a candidate pool
(by default SeedMiner's own mining, optionally broadened by --cands,
--phasefit, --mut, and/or --trace-houdini), keep only the candidates
that pass the initiation check (Init(relation) => candidate), and try
each survivor individually as forward-fixpoint's `initial_seed` --
exactly generalizing ff_seeded.py's single-fixed-source strategy to any
combination of this codebase's candidate-generating techniques.
"""

from __future__ import annotations

from pathlib import Path

from pyhorn_bnd.ff_houdini import FFHoudiniStatus, run_ff_houdini
from pyhorn_bnd.horn import parse_chc_file

EXAMPLES = Path(__file__).resolve().parents[1] / "examples"


def _write(tmp_path: Path, name: str, smt2: str) -> Path:
    path = tmp_path / name
    path.write_text(smt2)
    return path


# ---------------------------------------------------------------------------
# The flagship case: a cross-relation handoff where the fact Houdini needs
# for inductiveness (x>=0, on relation b) has no literal comparison atom
# anywhere for SeedMiner to weaken -- it only exists because a's own value
# (itself weakenable from a's fact rule) is copied across a relation
# boundary via argument position, not asserted directly. Neither --ff alone
# nor --seed-houdini alone can prove this; --ff-houdini, seeding forward
# propagation individually from a's own weakened fact-rule atom (x>=0 on
# *a*, whose closure under the step rules is what actually establishes the
# property), succeeds where both underlying techniques fail on their own.
# ---------------------------------------------------------------------------

_HANDOFF_GAP_SMT2 = """
(set-logic HORN)
(declare-var c Int)
(declare-var c1 Int)
(declare-var len Int)
(declare-var x Int)
(declare-var y Int)
(declare-var steps Int)
(declare-var y1 Int)
(declare-var steps1 Int)
(declare-rel a (Int Int))
(declare-rel b (Int Int Int))
(declare-rel fail ())

(rule (a 0 len))
(rule (=> (and (a c len) (< c len) (= c1 (+ c 1))) (a c1 len)))

(rule (=> (a c len) (b c 0 0)))

(rule (=> (and (b x y steps) (< steps 5)
               (= y1 (+ y (ite (>= x 0) 2 (- 2))))
               (= steps1 (+ steps 1)))
          (b x y1 steps1)))

(rule (=> (and (b x y steps) (not (= y (* 2 steps)))) fail))
(query fail)
"""


def test_ff_alone_and_seed_houdini_alone_both_fail_on_the_gap_example(tmp_path):
    """Ground truth for the flagship case below: confirms neither
    component alone can prove this input safe, so the SAFE verdict the
    combined test asserts is actually demonstrating something, not just
    re-deriving what one side already had on its own.
    """
    from pyhorn_bnd.forward_fixpoint import ForwardFixpointStatus, run_forward_fixpoint
    from pyhorn_bnd.houdini import HoudiniStatus, run_seed_houdini

    path = _write(tmp_path, "handoff_gap.smt2", _HANDOFF_GAP_SMT2)
    program = parse_chc_file(path, slice_program=False)

    ff_only = run_forward_fixpoint(program)
    assert ff_only.status is ForwardFixpointStatus.UNKNOWN

    seed_only = run_seed_houdini(program)
    assert seed_only.status is HoudiniStatus.UNKNOWN


def test_combined_succeeds_where_ff_alone_and_seed_houdini_alone_both_fail(
    tmp_path,
):
    """The flagship positive case: seeding forward-fixpoint individually
    from a candidate in the default (SeedMiner-mined) pool is enough,
    even though neither plain --ff (the full, literal init) nor plain
    --seed-houdini (syntactic mining plus MultiHoudini elimination, no
    forward propagation at all) can prove this input alone.
    """
    path = _write(tmp_path, "handoff_gap.smt2", _HANDOFF_GAP_SMT2)
    program = parse_chc_file(path, slice_program=False)

    result = run_ff_houdini(program)

    assert result.status is FFHoudiniStatus.SAFE
    assert result.invariants is not None
    assert result.winning_relation is not None
    assert result.winning_candidate is not None
    assert result.attempts >= 1
    assert result.candidates_sound <= result.candidates_gathered


# ---------------------------------------------------------------------------
# Delegation: whichever candidate settles the question, the underlying
# forward-fixpoint verdict must pass through unaltered.
# ---------------------------------------------------------------------------


def test_reports_safe_for_a_bounded_safe_program(tmp_path):
    smt2 = """
(declare-var x Int)
(declare-rel inv (Int))
(declare-rel fail ())
(rule (inv 0))
(rule (=> (and (inv x) (< x 5)) (inv (+ x 1))))
(rule (=> (and (inv x) (>= x 10)) fail))
(query fail)
"""
    path = _write(tmp_path, "bounded_safe.smt2", smt2)
    program = parse_chc_file(path, slice_program=False)

    result = run_ff_houdini(program)

    assert result.status is FFHoudiniStatus.SAFE
    assert result.attempts >= 1


def test_reports_unsafe_with_a_confirmed_counterexample(tmp_path):
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

    result = run_ff_houdini(program)

    assert result.status is FFHoudiniStatus.UNSAFE
    assert result.counterexample_model is not None
    assert result.violated_rule is not None
    assert result.winning_relation is not None


def test_reports_safe_for_a_relational_fact_the_default_pool_already_mines(
    tmp_path,
):
    """A relational fact (y == 2*x) plain seed-mining already finds
    unaided from the negated query -- with the default candidate pool
    (SeedMiner's own mining), this should resolve via that mined
    candidate's own individual forward propagation.
    """
    smt2 = """
(set-logic HORN)
(declare-var x Int)
(declare-var y Int)
(declare-var len Int)
(declare-var x1 Int)
(declare-var y1 Int)
(declare-rel inv (Int Int Int))
(declare-rel fail ())
(rule (inv 0 0 len))
(rule (=> (and (inv x y len) (< x len) (= x1 (+ x 1)) (= y1 (+ y 2))) (inv x1 y1 len)))
(rule (=> (and (inv x y len) (not (= y (* 2 x)))) fail))
(query fail)
"""
    path = _write(tmp_path, "relational.smt2", smt2)
    program = parse_chc_file(path, slice_program=False)

    result = run_ff_houdini(program)

    assert result.status is FFHoudiniStatus.SAFE


# ---------------------------------------------------------------------------
# UNKNOWN: a genuinely unprovable-by-this-mechanism input -- must terminate
# cleanly (never raise, never loop), and there is no whole-formula fallback
# to fall back on (see the module docstring).
# ---------------------------------------------------------------------------


def test_reports_unknown_when_no_individual_candidate_settles_it(tmp_path):
    """dillig46: x and w must be seeded together for x<=1 to be
    provable; no single candidate (x alone, y alone, z alone, or w
    alone -- nor any other single mined atom) suffices on its own, and
    this module never falls back to a joint/whole-formula attempt.
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
    path = _write(tmp_path, "trivially_unknown.smt2", smt2)
    program = parse_chc_file(path, slice_program=False)

    result = run_ff_houdini(program, ff_timeout_ms=500)

    assert result.status is FFHoudiniStatus.UNKNOWN
    assert result.winning_relation is None
    assert result.winning_candidate is None
    # Every sound candidate the pool offered was actually tried -- no
    # early stop, no fallback left over.
    assert result.attempts == result.candidates_sound


def test_reports_unknown_gracefully_with_an_empty_candidate_pool(tmp_path):
    """A relation with no mineable structure at all (an unconstrained
    fact and a no-op step) still terminates cleanly with UNKNOWN rather
    than raising, even though nothing ends up sound enough to try.
    """
    smt2 = """
(declare-var x Int)
(declare-rel inv (Int))
(declare-rel fail ())
(rule (inv x))
(rule (=> (inv x) (inv x)))
(rule (=> (and (inv x) (>= x 2)) fail))
(query fail)
"""
    path = _write(tmp_path, "no_candidates.smt2", smt2)
    program = parse_chc_file(path, slice_program=False)

    result = run_ff_houdini(program)

    assert result.status is FFHoudiniStatus.UNKNOWN
    assert result.attempts == 0


# ---------------------------------------------------------------------------
# Candidate-pool broadening: --cands / --phasefit / --mut / --trace-houdini
# are purely additive over the default (SeedMiner-mined) pool.
# ---------------------------------------------------------------------------


def test_user_supplied_cands_broaden_the_pool_and_can_be_the_winner(tmp_path):
    """A user-supplied candidate the default SeedMiner pool would never
    mine on its own (an arbitrary widening no literal in the program
    suggests) is merged in and can be the one that actually settles it.
    """
    smt2 = """
(declare-var x Int)
(declare-rel inv (Int))
(declare-rel fail ())
(rule (inv 0))
(rule (=> (and (inv x) (< x 5)) (inv (+ x 1))))
(rule (=> (and (inv x) (>= x 1000)) fail))
(query fail)
"""
    program_path = _write(tmp_path, "wide_bound.smt2", smt2)
    program = parse_chc_file(program_path, slice_program=False)

    cands_path = _write(
        tmp_path,
        "cands.smt2",
        """
(declare-fun inv (Int) Bool)
(define-fun inv ((x Int)) Bool
  (<= x 100))
""",
    )

    without_cands = run_ff_houdini(program)
    assert without_cands.status is FFHoudiniStatus.SAFE  # provable unaided too

    # --cands alone (no --seed-houdini): the pool is built "wrt the
    # options" -- just the user's own candidate(s), not the default
    # SeedMiner pool too. Still enough to prove it here.
    with_cands_only = run_ff_houdini(program, cands_path=cands_path)
    assert with_cands_only.status is FFHoudiniStatus.SAFE
    assert with_cands_only.candidates_gathered == 1

    # --cands *and* --seed-houdini: --seed-houdini is a genuine toggle
    # once another source narrowed the pool -- this is the union of the
    # previous two pools (not necessarily an exact sum: merge_candidate_maps
    # dedupes any candidate the two sources happen to produce syntactically
    # alike).
    with_cands_and_seed = run_ff_houdini(
        program, cands_path=cands_path, use_seed_houdini=True
    )
    assert with_cands_and_seed.status is FFHoudiniStatus.SAFE
    assert (
        with_cands_and_seed.candidates_gathered
        <= with_cands_only.candidates_gathered + without_cands.candidates_gathered
    )
    assert with_cands_and_seed.candidates_gathered > with_cands_only.candidates_gathered


def test_trace_houdini_alone_excludes_the_default_seed_pool(tmp_path):
    """--trace-houdini without --seed-houdini narrows the pool to just
    the trace-mined candidates -- not the default SeedMiner pool too --
    exactly like --cands does above. Adding --seed-houdini back genuinely
    broadens it again, since neither flag structurally forces the other
    the way --phasefit's own atom-harvesting requirement does.
    """
    path = _write(tmp_path, "handoff_gap.smt2", _HANDOFF_GAP_SMT2)
    program = parse_chc_file(path, slice_program=False)

    trace_only = run_ff_houdini(program, use_trace=True)
    trace_and_seed = run_ff_houdini(program, use_trace=True, use_seed_houdini=True)
    default_pool = run_ff_houdini(program)

    assert trace_and_seed.candidates_gathered > trace_only.candidates_gathered
    # Not necessarily an exact sum: merge_candidate_maps dedupes any
    # candidate the two sources happen to produce syntactically alike.
    assert (
        trace_and_seed.candidates_gathered
        <= trace_only.candidates_gathered + default_pool.candidates_gathered
    )


def test_mut_broadens_the_pool(tmp_path):
    smt2 = """
(declare-var x Int)
(declare-var y Int)
(declare-rel inv (Int Int))
(declare-rel fail ())
(rule (=> (and (= x 0) (= y 0)) (inv x y)))
(rule (=> (and (inv x y) (< x 5)) (inv (+ x 1) (+ y 1))))
(rule (=> (and (inv x y) (not (= x y))) fail))
(query fail)
"""
    path = _write(tmp_path, "relational_mut.smt2", smt2)
    program = parse_chc_file(path, slice_program=False)

    without_mut = run_ff_houdini(program)
    with_mut = run_ff_houdini(program, use_mut=True)

    assert with_mut.candidates_gathered >= without_mut.candidates_gathered
    assert with_mut.status is not FFHoudiniStatus.UNSAFE
    assert without_mut.status is not FFHoudiniStatus.UNSAFE


def test_never_reports_unsafe_for_a_genuinely_safe_program_regardless_of_pool(
    tmp_path,
):
    """Whatever candidate ends up seeding forward-fixpoint, it always
    passed the initiation check first (Init => candidate, verified
    internally), so this can never fabricate an UNSAFE verdict for a
    program that's actually safe -- regardless of which source
    contributed the winning candidate.
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
    path = _write(tmp_path, "relational_safe.smt2", smt2)
    program = parse_chc_file(path, slice_program=False)

    result = run_ff_houdini(program, use_mut=True, use_phasefit=True)

    assert result.status is not FFHoudiniStatus.UNSAFE


# ---------------------------------------------------------------------------
# CLI wiring: combinability with every other flag (the actual point of this
# redesign), and that plain --ff remains the one thing it cannot combine
# with.
# ---------------------------------------------------------------------------


def test_cli_ff_houdini_reports_success(tmp_path, capsys):
    from pyhorn_bnd.cli import main

    path = _write(tmp_path, "handoff_gap.smt2", _HANDOFF_GAP_SMT2)
    exit_code = main(["--ff-houdini", str(path)])

    assert exit_code == 0
    assert capsys.readouterr().out.strip() == "Success"


def test_cli_ff_houdini_json_reports_pool_and_winner(tmp_path, capsys):
    import json

    from pyhorn_bnd.cli import main

    path = _write(tmp_path, "handoff_gap.smt2", _HANDOFF_GAP_SMT2)
    main(["--ff-houdini", "--json", str(path)])
    out = json.loads(capsys.readouterr().out.splitlines()[0])

    assert out["status"] == "safe"
    assert out["attempts"] >= 1
    assert out["candidates_sound"] <= out["candidates_gathered"]
    assert out["winning_relation"] is not None
    assert out["winning_candidate"] is not None


def test_cli_ff_houdini_combines_with_seed_houdini(tmp_path, capsys):
    """--seed-houdini alongside bare --ff-houdini (nothing else given) is
    accepted as a (redundant but harmless) no-op, not an error --
    --ff-houdini already mines its own default pool regardless in that
    case. See test_cli_ff_houdini_seed_houdini_broadens_the_pool_once_narrowed
    below for the case where it does have a visible effect.
    """
    from pyhorn_bnd.cli import main

    path = _write(tmp_path, "handoff_gap.smt2", _HANDOFF_GAP_SMT2)
    exit_code = main(["--ff-houdini", "--seed-houdini", str(path)])

    assert exit_code == 0
    assert capsys.readouterr().out.strip() == "Success"


def test_cli_ff_houdini_seed_houdini_broadens_the_pool_once_narrowed(
    tmp_path, capsys
):
    """Once --trace-houdini (or --cands) narrows the pool to just what
    was actually asked for, --seed-houdini genuinely broadens it again --
    unlike the bare---ff-houdini case above, this combination is not a
    no-op.
    """
    import json

    from pyhorn_bnd.cli import main

    path = _write(tmp_path, "handoff_gap.smt2", _HANDOFF_GAP_SMT2)

    main(["--ff-houdini", "--trace-houdini", "--json", str(path)])
    without_seed_houdini = json.loads(capsys.readouterr().out.splitlines()[0])

    main(
        [
            "--ff-houdini",
            "--trace-houdini",
            "--seed-houdini",
            "--json",
            str(path),
        ]
    )
    with_seed_houdini = json.loads(capsys.readouterr().out.splitlines()[0])

    assert (
        with_seed_houdini["candidates_gathered"]
        > without_seed_houdini["candidates_gathered"]
    )


def test_cli_ff_houdini_combines_with_ff_seeded(tmp_path, capsys):
    """--ff-seeded alongside --ff-houdini is likewise accepted, with no
    separate effect -- its own strategy is --ff-houdini's default.
    """
    from pyhorn_bnd.cli import main

    path = _write(tmp_path, "handoff_gap.smt2", _HANDOFF_GAP_SMT2)
    exit_code = main(["--ff-houdini", "--ff-seeded", str(path)])

    assert exit_code == 0
    assert capsys.readouterr().out.strip() == "Success"


def test_cli_ff_houdini_combines_with_mut_phasefit_and_trace_houdini(
    tmp_path, capsys
):
    from pyhorn_bnd.cli import main

    path = _write(tmp_path, "handoff_gap.smt2", _HANDOFF_GAP_SMT2)
    exit_code = main(
        [
            "--ff-houdini",
            "--mut",
            "--phasefit",
            "--trace-houdini",
            str(path),
        ]
    )

    assert exit_code == 0
    assert capsys.readouterr().out.strip() == "Success"


def test_cli_ff_houdini_combines_with_cands(tmp_path, capsys):
    from pyhorn_bnd.cli import main

    program_path = _write(tmp_path, "handoff_gap.smt2", _HANDOFF_GAP_SMT2)
    cands_path = _write(
        tmp_path,
        "cands.smt2",
        """
(declare-fun a (Int Int) Bool)
(define-fun a ((c Int) (len Int)) Bool
  (>= c 0))
""",
    )
    exit_code = main(
        ["--ff-houdini", "--cands", str(cands_path), str(program_path)]
    )

    assert exit_code == 0
    assert capsys.readouterr().out.strip() == "Success"


def test_cli_ff_houdini_and_trace_houdini_and_cands_all_together(
    tmp_path, capsys
):
    """A combination the plain Houdini pipeline explicitly rejects
    (--trace-houdini cannot be combined with --cands there) is fine here,
    since --ff-houdini builds its own pool directly rather than
    delegating to run_trace_houdini().
    """
    from pyhorn_bnd.cli import main

    program_path = _write(tmp_path, "handoff_gap.smt2", _HANDOFF_GAP_SMT2)
    cands_path = _write(
        tmp_path,
        "cands.smt2",
        """
(declare-fun a (Int Int) Bool)
(define-fun a ((c Int) (len Int)) Bool
  (>= c 0))
""",
    )
    exit_code = main(
        [
            "--ff-houdini",
            "--trace-houdini",
            "--cands",
            str(cands_path),
            str(program_path),
        ]
    )

    assert exit_code == 0
    assert capsys.readouterr().out.strip() == "Success"


def test_cli_plain_trace_houdini_still_rejects_cands(tmp_path, capsys):
    """Without --ff-houdini, the original restriction on run_trace_houdini()
    still applies."""
    import pytest

    from pyhorn_bnd.cli import main

    program_path = _write(tmp_path, "handoff_gap.smt2", _HANDOFF_GAP_SMT2)
    cands_path = _write(
        tmp_path,
        "cands.smt2",
        """
(declare-fun a (Int Int) Bool)
(define-fun a ((c Int) (len Int)) Bool
  (>= c 0))
""",
    )
    with pytest.raises(SystemExit) as exc_info:
        main(["--trace-houdini", "--cands", str(cands_path), str(program_path)])
    assert exc_info.value.code == 2
    assert "--trace-houdini cannot be combined with --cands" in (
        capsys.readouterr().err
    )


def test_cli_ff_houdini_rejects_combination_with_ff(tmp_path, capsys):
    import pytest

    from pyhorn_bnd.cli import main

    path = _write(tmp_path, "handoff_gap.smt2", _HANDOFF_GAP_SMT2)
    with pytest.raises(SystemExit) as exc_info:
        main(["--ff", "--ff-houdini", str(path)])
    assert exc_info.value.code == 2
    assert "--ff-houdini" in capsys.readouterr().err


def test_cli_ff_houdini_mut_alone_does_not_require_seed_houdini(tmp_path, capsys):
    """--mut alongside --ff-houdini (with no --seed-houdini/--cands/
    --trace-houdini/--phasefit) is not rejected by the "--mut requires
    one of ..." usage check -- --ff-houdini satisfies it on its own.
    """
    from pyhorn_bnd.cli import main

    path = _write(tmp_path, "handoff_gap.smt2", _HANDOFF_GAP_SMT2)
    exit_code = main(["--ff-houdini", "--mut", str(path)])

    assert exit_code == 0


def test_cli_ff_houdini_max_rounds_flag_no_longer_exists(tmp_path, capsys):
    """The old alternation's round budget has no meaning for this
    module's individual-candidate-propagation mechanism (see the module
    docstring) and was removed along with the alternation itself.
    """
    import pytest

    from pyhorn_bnd.cli import main

    path = _write(tmp_path, "handoff_gap.smt2", _HANDOFF_GAP_SMT2)
    with pytest.raises(SystemExit) as exc_info:
        main(["--ff-houdini", "--ff-houdini-max-rounds", "5", str(path)])
    assert exc_info.value.code == 2
