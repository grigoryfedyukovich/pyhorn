"""Tests for :mod:`pyhorn_bnd.candidate_validation` -- bounded candidate reachability validation."""

from __future__ import annotations

import textwrap
from pathlib import Path

import pytest
import z3

from pyhorn_bnd import MultiHoudini, SeedMiner, parse_chc_file
from pyhorn_bnd.candidate_validation import (
    DEFAULT_CANDIDATE_BOUND,
    CandidateReachability,
    dump_promising_candidate_files,
    render_candidate_verification_smt2,
    validate_candidate_reachability,
    validate_removed_candidate,
)
from pyhorn_bnd.houdini import RemovedCandidate
from pyhorn_bnd.vc import VerificationConditionBuilder

ROOT = Path(__file__).resolve().parents[1]
EXAMPLES = ROOT / "examples" / "seed_houdini"


def _write(tmp_path: Path, name: str, content: str) -> Path:
    p = tmp_path / name
    p.write_text(textwrap.dedent(content), encoding="utf-8")
    return p


def _relation(program, name: str) -> z3.FuncDeclRef:
    return next(r for r in program.relations if str(r.name()) == name)


# ---------------------------------------------------------------------------
# validate_candidate_reachability -- real counter_safe.smt2 removals
# ---------------------------------------------------------------------------


class TestValidateCandidateReachabilityOnCounterSafe:
    def _mine_and_run(self):
        program = parse_chc_file(EXAMPLES / "counter_safe.smt2", slice_program=False)
        seeds = SeedMiner(program).mine()
        result = MultiHoudini(program, seeds.variables, timeout_ms=5_000).run(
            seeds.candidates, seed_result=seeds
        )
        return program, result

    def test_success_status_unaffected_by_validation_being_available(self):
        _, result = self._mine_and_run()
        assert result.status.value == "success"
        assert len(result.removed_candidates) > 0

    def test_step_rule_removal_at_x_equals_0_is_reachable_at_depth_2(self):
        """The removed candidate is 'x = 0'; the fact itself (depth 1) gives
        x=0, satisfying it -- the violation only appears one self-loop step
        later, at depth 2, once x becomes 1."""
        program, result = self._mine_and_run()
        rc = next(rc for rc in result.removed_candidates if rc.pre_state == "__inv_0 = 0")
        v = validate_removed_candidate(program, result.variables, rc, upto=10)
        assert v.status is CandidateReachability.REACHABLE
        assert v.witness_depth == 2

    def test_step_rule_removal_at_x_equals_9_is_reachable_at_depth_11(self):
        """The removed candidate is 'x < 10'; it is falsified once inv holds
        x=10 directly (reachable via 1 fact + 10 self-loop steps), not by
        the x=9 pre-state alone -- hence depth 11, not 10."""
        program, result = self._mine_and_run()
        rc = next(rc for rc in result.removed_candidates if rc.pre_state == "__inv_0 = 9")
        v = validate_removed_candidate(program, result.variables, rc, upto=11)
        assert v.status is CandidateReachability.REACHABLE
        assert v.witness_depth == 11

    def test_x_equals_9_witness_not_found_when_bound_too_small(self):
        """Falsifying 'x < 10' genuinely requires reaching inv with x=10,
        i.e. depth 11; a bound of 5 must not find it, proving the bound is
        honestly respected rather than silently ignored or over-searched."""
        program, result = self._mine_and_run()
        rc = next(rc for rc in result.removed_candidates if rc.pre_state == "__inv_0 = 9")
        v = validate_removed_candidate(program, result.variables, rc, upto=5)
        assert v.status is CandidateReachability.NOT_FOUND
        assert v.checked_upto == 5

    def test_x_equals_9_witness_not_found_with_default_bound(self):
        """With the library default (--candidate-bound 10 at the CLI), the depth-11
        witness for this specific removal is just out of reach -- a direct
        regression guard for the depth semantics, not a claim that
        --candidate-bound 10 is somehow wrong."""
        program, result = self._mine_and_run()
        rc = next(rc for rc in result.removed_candidates if rc.pre_state == "__inv_0 = 9")
        v = validate_removed_candidate(program, result.variables, rc)
        assert v.status is CandidateReachability.NOT_FOUND
        assert v.checked_upto == DEFAULT_CANDIDATE_BOUND == 10

    def test_fact_rule_removal_is_not_applicable(self):
        program, result = self._mine_and_run()
        rc = next(rc for rc in result.removed_candidates if rc.pre_state is None)
        v = validate_removed_candidate(program, result.variables, rc, upto=10)
        assert v.status is CandidateReachability.NOT_APPLICABLE
        assert v.checks_performed == 0
        assert v.witness_depth is None

    def test_checks_performed_matches_depths_tried_for_single_path_program(self):
        """counter_safe has exactly one path shape (fact, then a single
        self-loop rule), so exactly one trace exists per depth: the number
        of checks performed to find a depth-d witness must be exactly d."""
        program, result = self._mine_and_run()
        rc = next(rc for rc in result.removed_candidates if rc.pre_state == "__inv_0 = 9")
        v = validate_removed_candidate(program, result.variables, rc, upto=11)
        assert v.checks_performed == 11

    def test_elapsed_seconds_is_non_negative(self):
        program, result = self._mine_and_run()
        rc = next(rc for rc in result.removed_candidates if rc.pre_state == "__inv_0 = 0")
        v = validate_removed_candidate(program, result.variables, rc, upto=10)
        assert v.elapsed_seconds >= 0.0

    def test_shared_builder_gives_consistent_answers_across_candidates(self):
        """A VerificationConditionBuilder passed in and reused across
        multiple validate calls must not leak state between them."""
        program, result = self._mine_and_run()
        builder = VerificationConditionBuilder(program)
        results = {
            rc.pre_state: validate_removed_candidate(
                program, result.variables, rc, upto=11, builder=builder
            )
            for rc in result.removed_candidates
            if rc.pre_state is not None
        }
        assert results["__inv_0 = 0"].status is CandidateReachability.REACHABLE
        assert results["__inv_0 = 0"].witness_depth == 2
        assert results["__inv_0 = 9"].status is CandidateReachability.REACHABLE
        assert results["__inv_0 = 9"].witness_depth == 11


# ---------------------------------------------------------------------------
# Regression: a candidate that does not mention every canonical variable of
# its relation must get the same (correctly REACHABLE) verdict regardless of
# which other, irrelevant candidates are active alongside it. Before the fix,
# validate_candidate_reachability pinned the CTI's full countermodel -- including
# an arbitrary value Z3 picked for the variable the candidate does not
# constrain -- so the exact same genuinely-bad removal could spuriously come
# back NOT_FOUND (falsely "promising") depending on what else was in the
# active candidate set, purely because that changed which witness the
# solver happened to report for the irrelevant variable.
# ---------------------------------------------------------------------------


class TestDontCareVariableDoesNotAffectVerdict:
    """itp(m, i): m advances by 66 and i by 55 every step, from (0, 0).
    'm <= 1' is genuinely non-inductive (m jumps to 66 in one step) --
    entirely independent of i, which no candidate here ever mentions."""

    def _program(self, tmp_path: Path) -> Path:
        return _write(
            tmp_path,
            "dont_care.smt2",
            """\
            (declare-rel itp (Int Int))
            (declare-var m Int)
            (declare-var m1 Int)
            (declare-var i Int)
            (declare-var i1 Int)
            (declare-rel fail ())

            (rule (=> (and (= m 0) (= i 0)) (itp m i)))

            (rule (=>
                (and (itp m i) (= i1 (+ i 55)) (= m1 (+ m 66)))
                (itp m1 i1)
              )
            )

            (rule (=> (and (itp m i) (not (>= (+ m i) 0))) fail))
            (query fail)
            """,
        )

    def _verdict_for_m_leq_1(self, tmp_path: Path, *, include_m_leq_2: bool):
        source = self._program(tmp_path)
        program = parse_chc_file(source, slice_program=False)
        variables = SeedMiner(program).variables
        itp = _relation(program, "itp")
        m, _i = variables[itp]  # i is deliberately unused: the don't-care variable

        candidates = (m >= 0, m <= 1, *((m <= 2,) if include_m_leq_2 else ()))
        result = MultiHoudini(program, variables, timeout_ms=5_000).run({itp: candidates})
        rc = next(
            rc
            for rc in result.removed_candidates
            if rc.candidate == z3.simplify(m <= 1).sexpr()
        )
        return validate_removed_candidate(program, variables, rc, upto=10)

    def test_reachable_verdict_for_m_leq_1_with_three_candidates(self, tmp_path: Path):
        v = self._verdict_for_m_leq_1(tmp_path, include_m_leq_2=True)
        assert v.status is CandidateReachability.REACHABLE

    def test_reachable_verdict_for_m_leq_1_with_two_candidates(self, tmp_path: Path):
        """The exact scenario reported: removing 'm <= 1' is refuted at
        i=0 when 'm <= 2' is also active, but at some other, arbitrary i
        once it is not -- the verdict must not flip because of that."""
        v = self._verdict_for_m_leq_1(tmp_path, include_m_leq_2=False)
        assert v.status is CandidateReachability.REACHABLE

    def test_verdict_is_identical_regardless_of_which_other_candidates_are_active(
        self, tmp_path: Path
    ):
        with_extra = self._verdict_for_m_leq_1(tmp_path, include_m_leq_2=True)
        without_extra = self._verdict_for_m_leq_1(tmp_path, include_m_leq_2=False)
        assert with_extra.status is without_extra.status is CandidateReachability.REACHABLE
        assert with_extra.witness_depth == without_extra.witness_depth == 2


# ---------------------------------------------------------------------------
# validate_candidate_reachability -- a genuine "needs a helper lemma" scenario
# ---------------------------------------------------------------------------


class TestPotentiallyPromisingCandidate:
    """x counts 0..5; y counts 100 down to 95 in lockstep (y == 100 - x
    always). 'y >= 1' alone is not locally inductive (Houdini can't rule out
    y dropping to 0 without knowing it's tied to x), but the pre-state that
    would refute it (y == 1, reachable only if x == 99) is never actually
    reachable, since x is bounded by the loop guard to at most 5."""

    def _program_and_relation(self, tmp_path: Path):
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
        program = parse_chc_file(source, slice_program=False)
        return program, _relation(program, "inv")

    def test_weak_candidate_alone_is_removed_and_reported_not_found(self, tmp_path: Path):
        program, inv = self._program_and_relation(tmp_path)
        variables = SeedMiner(program).variables
        _, y = variables[inv]

        result = MultiHoudini(program, variables, timeout_ms=5_000).run({inv: (y >= 1,)})
        assert len(result.removed_candidates) == 1
        rc = result.removed_candidates[0]
        assert rc.candidate == z3.simplify(y >= 1).sexpr()

        v = validate_removed_candidate(program, variables, rc, upto=10)
        assert v.status is CandidateReachability.NOT_FOUND
        assert v.checked_upto == 10

    def test_helper_lemma_lets_weak_candidate_survive_filtering(self, tmp_path: Path):
        """Confirms the scenario is genuinely a 'needs a helper lemma' case,
        not just a badly chosen candidate: paired with y == 100 - x, 'y >= 1'
        is no longer refutable by any single-step transition, so neither
        candidate gets removed by Houdini's local filtering."""
        program, inv = self._program_and_relation(tmp_path)
        variables = SeedMiner(program).variables
        x, y = variables[inv]

        result = MultiHoudini(program, variables, timeout_ms=5_000).run(
            {inv: (y >= 1, y == 100 - x)}
        )
        assert len(result.removed_candidates) == 0

    def test_full_invariant_set_including_helper_proves_safety(self, tmp_path: Path):
        """y == 100 - x alone bounds y in terms of x but not x itself; the
        loop guard caps x at 5, so the complete (all locally inductive,
        together sufficient) invariant set also needs x <= 5."""
        program, inv = self._program_and_relation(tmp_path)
        variables = SeedMiner(program).variables
        x, y = variables[inv]

        result = MultiHoudini(program, variables, timeout_ms=5_000).run(
            {inv: (y >= 1, y == 100 - x, x <= 5)}
        )
        assert result.status.value == "success"
        assert len(result.removed_candidates) == 0


# ---------------------------------------------------------------------------
# validate_candidate_reachability -- direct relation/values API, branching program
# ---------------------------------------------------------------------------


class TestValidateCandidateReachabilityDirectApi:
    def test_unreachable_relation_reports_not_found_with_zero_checks_if_no_traces(
        self, tmp_path: Path
    ):
        """A relation with no incoming rule from anywhere yields zero
        candidate traces at every depth: NOT_FOUND, 0 checks, regardless of
        the candidate supplied (the trace search never gets far enough to
        use it)."""
        source = _write(
            tmp_path,
            "dead.smt2",
            """\
            (declare-var x Int)
            (declare-rel live (Int))
            (declare-rel unreachable (Int))
            (declare-rel fail ())
            (rule (live 0))
            (rule (=> (unreachable x) fail))
            (rule (=> (and (live x) (> x 100)) fail))
            """,
        )
        program = parse_chc_file(source, slice_program=False)
        dead = _relation(program, "unreachable")
        v = validate_candidate_reachability(program, dead, z3.BoolVal(True), (), upto=5)
        assert v.status is CandidateReachability.NOT_FOUND
        assert v.checks_performed == 0

    def test_reachable_via_a_branch_not_taken_by_every_path(self, tmp_path: Path):
        """Two rules produce 'mid': the branch reaching x=1 must be found
        even though a sibling branch (reaching x=0) also exists at the same
        depth -- confirms all traces per depth are actually tried, not just
        the first one found."""
        source = _write(
            tmp_path,
            "branch.smt2",
            """\
            (declare-var x Int)
            (declare-rel start (Int))
            (declare-rel mid (Int))
            (declare-rel fail ())
            (rule (start 0))
            (rule (=> (start x) (mid 0)))
            (rule (=> (start x) (mid 1)))
            (rule (=> (and (mid x) (> x 100)) fail))
            """,
        )
        program = parse_chc_file(source, slice_program=False)
        mid = _relation(program, "mid")
        variables = SeedMiner(program).variables
        (mid_var,) = variables[mid]
        # "mid's argument != 1" is violated exactly when the x=1 branch is
        # taken; the sibling branch reaching mid=0 must not distract the
        # search away from it.
        v = validate_candidate_reachability(program, mid, mid_var != 1, (mid_var,), upto=5)
        assert v.status is CandidateReachability.REACHABLE
        assert v.witness_depth == 2

    def test_upto_zero_traces_yields_nothing(self, tmp_path: Path):
        program, inv = TestPotentiallyPromisingCandidate()._program_and_relation(tmp_path)
        variables = SeedMiner(program).variables
        x, y = variables[inv]
        # upto must be >= 1 for the CLI, but the underlying function should
        # not crash if handed a degenerate range; range(1, 1) is simply empty.
        v = validate_candidate_reachability(program, inv, y >= 1, (x, y), upto=0)
        assert v.status is CandidateReachability.NOT_FOUND
        assert v.checks_performed == 0

    def test_fact_rule_relation_is_checked_like_any_other(self, tmp_path: Path):
        """Unlike the old rule-rechaining design, there is no special case
        here for a relation only ever produced by a fact rule -- a trace of
        length 1 (just the fact) is one more ordinary trace in the search.
        (validate_removed_candidate still fast-paths this via
        NOT_APPLICABLE for efficiency; this test exercises the underlying
        mechanism directly, without that fast path.)"""
        program, inv = TestPotentiallyPromisingCandidate()._program_and_relation(tmp_path)
        variables = SeedMiner(program).variables
        x, y = variables[inv]
        # (0, 100) is the fact's own value; checking whether it can be
        # anything else finds nothing, since the fact fixes it exactly.
        v = validate_candidate_reachability(
            program, inv, z3.And(x == 0, y == 100), (x, y), upto=1
        )
        assert v.status is CandidateReachability.NOT_FOUND
        assert v.checks_performed == 1

        v = validate_candidate_reachability(
            program, inv, z3.And(x == 0, y == 999), (x, y), upto=1
        )
        assert v.status is CandidateReachability.REACHABLE
        assert v.witness_depth == 1


# ---------------------------------------------------------------------------
# validate_removed_candidate -- NOT_APPLICABLE via a hand-built RemovedCandidate
# ---------------------------------------------------------------------------


def test_validate_removed_candidate_without_pre_relation_is_not_applicable():
    """A RemovedCandidate built without pre_relation/pre_values (e.g. by code
    that predates this feature, or constructed directly in a test) must be
    treated as not-applicable rather than crash."""
    program = parse_chc_file(EXAMPLES / "counter_safe.smt2", slice_program=False)
    variables = SeedMiner(program).variables
    rc = RemovedCandidate(
        relation="inv",
        candidate="(= x 0)",
        rule_id=0,
        rule="r0: ENTRY -> inv",
        pre_state=None,
        post_state="__inv_0 = 0",
        full_model="[]",
    )
    v = validate_removed_candidate(program, variables, rc, upto=10)
    assert v.status is CandidateReachability.NOT_APPLICABLE


# ---------------------------------------------------------------------------
# render_candidate_verification_smt2 / dump_promising_candidate_files
# ---------------------------------------------------------------------------


class TestRenderCandidateVerificationSmt2:
    def _helper_lemma_program(self, tmp_path: Path):
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
        program = parse_chc_file(source, slice_program=False)
        variables = SeedMiner(program).variables
        inv = _relation(program, "inv")
        _, y = variables[inv]
        result = MultiHoudini(program, variables, timeout_ms=5_000).run({inv: (y >= 1,)})
        rc = result.removed_candidates[0]
        return program, variables, rc

    def test_generated_file_reparses_successfully(self, tmp_path: Path):
        program, variables, rc = self._helper_lemma_program(tmp_path)
        text = render_candidate_verification_smt2(program, variables, rc)
        out = tmp_path / "generated.smt2"
        out.write_text(text, encoding="utf-8")
        reparsed = parse_chc_file(out, slice_program=False)
        assert len(reparsed.rules) == 3  # fact, step, new property

    def test_generated_property_matches_the_dropped_candidate(self, tmp_path: Path):
        program, variables, rc = self._helper_lemma_program(tmp_path)
        text = render_candidate_verification_smt2(program, variables, rc)
        assert rc.candidate in text

    def test_original_query_relation_and_its_rule_are_dropped(self, tmp_path: Path):
        """'fail' and the rule reaching it must not appear -- the new
        property replaces the original one rather than supplementing it."""
        program, variables, rc = self._helper_lemma_program(tmp_path)
        text = render_candidate_verification_smt2(program, variables, rc)
        assert "fail" not in text

    def test_fact_rule_is_rendered_without_a_vacuous_forall(self, tmp_path: Path):
        program, variables, rc = self._helper_lemma_program(tmp_path)
        text = render_candidate_verification_smt2(program, variables, rc)
        assert "(assert (inv 0 100))" in text

    def test_ground_truth_bounded_exploration_confirms_no_counterexample(
        self, tmp_path: Path
    ):
        """The whole point: an independent, non-Houdini check (plain bounded
        exploration) on the generated file must agree that the candidate
        holds up to the depth the real loop can reach (6 iterations here)."""
        from pyhorn_bnd.explorer import BoundedExplorer, ExplorationStatus

        program, variables, rc = self._helper_lemma_program(tmp_path)
        text = render_candidate_verification_smt2(program, variables, rc)
        out = tmp_path / "generated.smt2"
        out.write_text(text, encoding="utf-8")
        reparsed = parse_chc_file(out, slice_program=False)

        explorer = BoundedExplorer(reparsed, timeout_ms=5_000)
        result = explorer.explore(upto=10)
        assert result.status is ExplorationStatus.BOUNDED_SAFE

    def test_ground_truth_bounded_exploration_finds_counterexample_for_false_candidate(
        self,
    ):
        """Negative control: a genuinely false candidate's generated file
        must show a real counterexample under the same independent check,
        proving the generator does not just always look 'promising'."""
        from pyhorn_bnd.explorer import BoundedExplorer, ExplorationStatus

        program = parse_chc_file(EXAMPLES / "counter_safe.smt2", slice_program=False)
        seeds = SeedMiner(program).mine()
        result = MultiHoudini(program, seeds.variables, timeout_ms=5_000).run(
            seeds.candidates, seed_result=seeds
        )
        rc = next(rc for rc in result.removed_candidates if rc.pre_state == "__inv_0 = 0")

        text = render_candidate_verification_smt2(program, seeds.variables, rc)
        import tempfile

        with tempfile.TemporaryDirectory() as d:
            out = Path(d) / "generated.smt2"
            out.write_text(text, encoding="utf-8")
            reparsed = parse_chc_file(out, slice_program=False)
            explorer = BoundedExplorer(reparsed, timeout_ms=5_000)
            exploration = explorer.explore(upto=10)
        assert exploration.status is ExplorationStatus.COUNTEREXAMPLE

    def test_header_lines_rendered_as_comments(self, tmp_path: Path):
        program, variables, rc = self._helper_lemma_program(tmp_path)
        text = render_candidate_verification_smt2(
            program, variables, rc, header="line one\nline two"
        )
        lines = text.splitlines()
        assert lines[0] == "; line one"
        assert lines[1] == "; line two"

    def test_unknown_relation_name_raises_key_error(self, tmp_path: Path):
        program, variables, rc = self._helper_lemma_program(tmp_path)
        bogus = RemovedCandidate(
            relation="not_a_real_relation",
            candidate=rc.candidate,
            rule_id=rc.rule_id,
            rule=rc.rule,
            pre_state=rc.pre_state,
            post_state=rc.post_state,
            full_model=rc.full_model,
        )
        with pytest.raises(KeyError):
            render_candidate_verification_smt2(program, variables, bogus)


class TestDumpPromisingCandidateFiles:
    def _helper_lemma_run(self, tmp_path: Path):
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
        program = parse_chc_file(source, slice_program=False)
        variables = SeedMiner(program).variables
        inv = _relation(program, "inv")
        _, y = variables[inv]
        result = MultiHoudini(program, variables, timeout_ms=5_000).run({inv: (y >= 1,)})
        verdict = validate_removed_candidate(
            program, variables, result.removed_candidates[0], upto=10
        )
        return program, variables, result.removed_candidates, (verdict,)

    def test_writes_one_file_for_not_found_candidate(self, tmp_path: Path):
        program, variables, removed, verdicts = self._helper_lemma_run(tmp_path)
        out_dir = tmp_path / "cti_files"
        written = dump_promising_candidate_files(program, variables, removed, verdicts, out_dir)
        assert len(written) == 1
        assert 0 in written
        assert written[0].exists()
        assert written[0].parent == out_dir

    def test_output_directory_created_if_missing(self, tmp_path: Path):
        program, variables, removed, verdicts = self._helper_lemma_run(tmp_path)
        out_dir = tmp_path / "does" / "not" / "exist" / "yet"
        assert not out_dir.exists()
        dump_promising_candidate_files(program, variables, removed, verdicts, out_dir)
        assert out_dir.exists()

    def test_reachable_candidates_are_not_written(self, tmp_path: Path):
        program = parse_chc_file(EXAMPLES / "counter_safe.smt2", slice_program=False)
        seeds = SeedMiner(program).mine()
        result = MultiHoudini(program, seeds.variables, timeout_ms=5_000).run(
            seeds.candidates, seed_result=seeds
        )
        builder = VerificationConditionBuilder(program)
        # upto=11: the 'x < 10' removal's violating state (x=10) is one step
        # further than the deepest pre-state Houdini itself reported.
        verdicts = tuple(
            validate_removed_candidate(program, seeds.variables, rc, upto=11, builder=builder)
            for rc in result.removed_candidates
        )
        # every removed candidate in counter_safe.smt2 is either REACHABLE
        # or NOT_APPLICABLE (fact rule); none should be NOT_FOUND.
        assert all(c.status is not CandidateReachability.NOT_FOUND for c in verdicts)
        out_dir = tmp_path / "cti_files"
        written = dump_promising_candidate_files(
            program, seeds.variables, result.removed_candidates, verdicts, out_dir
        )
        assert written == {}

    def test_filenames_are_deterministic_across_runs(self, tmp_path: Path):
        program, variables, removed, verdicts = self._helper_lemma_run(tmp_path)
        first = dump_promising_candidate_files(program, variables, removed, verdicts, tmp_path / "a")
        second = dump_promising_candidate_files(program, variables, removed, verdicts, tmp_path / "b")
        assert first[0].name == second[0].name

    def test_rerun_overwrites_rather_than_duplicates(self, tmp_path: Path):
        program, variables, removed, verdicts = self._helper_lemma_run(tmp_path)
        out_dir = tmp_path / "cti_files"
        dump_promising_candidate_files(program, variables, removed, verdicts, out_dir)
        dump_promising_candidate_files(program, variables, removed, verdicts, out_dir)
        assert len(list(out_dir.glob("*.smt2"))) == 1
