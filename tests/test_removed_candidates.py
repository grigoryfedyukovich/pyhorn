"""Tests for the RemovedCandidate counterexample feature.

Every removed candidate must carry:
  - relation name (str)
  - candidate s-expression (str)
  - rule_id / rule short description
  - pre_state: "var = val, ..." for the source predicate, or None for facts
  - post_state: "var = val, ..." for the destination predicate
  - full_model: str(z3.ModelRef)

The pre/post state strings are evaluated from the induction counterexample
model, giving the concrete variable assignments that witness the violation.
"""

from __future__ import annotations

import json
from pathlib import Path

import z3

from pyhorn_bnd import parse_chc_file
from pyhorn_bnd.cli import _format_removed_candidate, main
from pyhorn_bnd.houdini import HoudiniStatus, MultiHoudini, RemovedCandidate
from pyhorn_bnd.seedminer import SeedMiner

ROOT = Path(__file__).resolve().parents[1]
EXAMPLES = ROOT / "examples" / "seed_houdini"


def _relation(program, name: str) -> z3.FuncDeclRef:
    return next(r for r in program.relations if str(r.name()) == name)


# ---------------------------------------------------------------------------
# Core: RemovedCandidate is populated on every filtered candidate
# ---------------------------------------------------------------------------


class TestRemovedCandidatePopulated:

    def _run(self, extra_candidate: z3.BoolRef | None = None):
        """Run MultiHoudini on counter_safe with an injected non-inductive candidate."""
        program = parse_chc_file(EXAMPLES / "counter_safe.smt2", slice_program=False)
        seeds = SeedMiner(program).mine()
        inv = _relation(program, "inv")
        variable = seeds.variables[inv][0]

        # (== __inv_0 0) is NOT inductive — will be removed by Houdini
        cands: set[z3.BoolRef] = {variable >= 0, variable <= 10, variable == 0}
        if extra_candidate is not None:
            cands.add(extra_candidate)

        result = MultiHoudini(program, seeds.variables, timeout_ms=5_000).run(
            {inv: cands}
        )
        return result, inv, variable

    def test_removed_candidates_is_non_empty(self):
        result, _, _ = self._run()
        assert len(result.removed_candidates) >= 1

    def test_removed_candidate_type(self):
        result, _, _ = self._run()
        for rc in result.removed_candidates:
            assert isinstance(rc, RemovedCandidate)

    def test_removed_candidate_relation_name(self):
        result, _, _ = self._run()
        for rc in result.removed_candidates:
            assert rc.relation == "inv"

    def test_removed_candidate_has_candidate_sexpr(self):
        result, _, _ = self._run()
        for rc in result.removed_candidates:
            assert isinstance(rc.candidate, str)
            assert len(rc.candidate) > 0

    def test_removed_candidate_rule_id_is_int(self):
        result, _, _ = self._run()
        for rc in result.removed_candidates:
            assert isinstance(rc.rule_id, int)

    def test_removed_candidate_rule_is_str(self):
        result, _, _ = self._run()
        for rc in result.removed_candidates:
            assert isinstance(rc.rule, str)
            assert len(rc.rule) > 0

    def test_removed_candidate_post_state_is_str(self):
        result, _, _ = self._run()
        for rc in result.removed_candidates:
            assert isinstance(rc.post_state, str)
            assert len(rc.post_state) > 0

    def test_removed_candidate_pre_state_is_str_or_none(self):
        result, _, _ = self._run()
        for rc in result.removed_candidates:
            assert rc.pre_state is None or isinstance(rc.pre_state, str)

    def test_removed_candidate_full_model_is_str(self):
        result, _, _ = self._run()
        for rc in result.removed_candidates:
            assert isinstance(rc.full_model, str)
            assert len(rc.full_model) > 0

    def test_removed_candidate_count_matches_statistics(self):
        result, _, _ = self._run()
        assert len(result.removed_candidates) == result.statistics.candidates_removed

    def test_no_removed_candidates_when_all_inductive(self):
        """Only inductive candidates supplied: nothing should be removed."""
        program = parse_chc_file(EXAMPLES / "counter_safe.smt2", slice_program=False)
        seeds = SeedMiner(program).mine()
        inv = _relation(program, "inv")
        variable = seeds.variables[inv][0]

        # Both are inductive for this benchmark
        result = MultiHoudini(program, seeds.variables, timeout_ms=5_000).run(
            {inv: (variable >= 0, variable <= 10)}
        )
        assert result.status is HoudiniStatus.SUCCESS
        assert result.removed_candidates == ()
        assert result.statistics.candidates_removed == 0


# ---------------------------------------------------------------------------
# Counterexample witness correctness
# ---------------------------------------------------------------------------


class TestRemovedCandidateWitness:

    def _removed_inv_eq_zero(self):
        """Return the RemovedCandidate for (== __inv_0 0) on counter_safe."""
        program = parse_chc_file(EXAMPLES / "counter_safe.smt2", slice_program=False)
        seeds = SeedMiner(program).mine()
        inv = _relation(program, "inv")
        variable = seeds.variables[inv][0]
        result = MultiHoudini(program, seeds.variables, timeout_ms=5_000).run(
            {inv: (variable >= 0, variable <= 10, variable == 0)}
        )
        # Exactly one candidate is removed: (== __inv_0 0)
        eq_zero_sexp = z3.simplify(variable == 0).sexpr()
        removed = [rc for rc in result.removed_candidates if rc.candidate == eq_zero_sexp]
        assert removed, f"Expected {eq_zero_sexp!r} in removed_candidates"
        return removed[0], variable

    def test_post_state_contains_variable_name(self):
        rc, variable = self._removed_inv_eq_zero()
        # post_state must reference the canonical variable name
        assert str(variable) in rc.post_state

    def test_post_state_contains_equals_sign(self):
        rc, _ = self._removed_inv_eq_zero()
        assert "=" in rc.post_state

    def test_post_state_value_violates_candidate(self):
        """The post-state value must actually violate (== __inv_0 0), i.e., != 0."""
        rc, variable = self._removed_inv_eq_zero()
        # Parse "var = val, ..." — the value for 'variable' must be != 0
        # The post_state format is "varname = value[, ...]"
        assignments = {
            k.strip(): v.strip()
            for part in rc.post_state.split(",")
            for k, v in [part.split("=", 1)]
        }
        var_name = str(variable)
        assert var_name in assignments
        val = int(assignments[var_name])
        assert val != 0, f"Post-state value {val} should violate (== {var_name} 0)"

    def test_pre_state_is_not_none_for_step_rule(self):
        """counter_safe has a step rule (inv -> inv), so pre_state must be set."""
        rc, _ = self._removed_inv_eq_zero()
        assert rc.pre_state is not None

    def test_pre_state_contains_variable_name(self):
        rc, variable = self._removed_inv_eq_zero()
        assert rc.pre_state is not None
        assert str(variable) in rc.pre_state


# ---------------------------------------------------------------------------
# Formatting
# ---------------------------------------------------------------------------


class TestFormatRemovedCandidate:

    def _make_rc(self, *, pre_state: str | None) -> RemovedCandidate:
        return RemovedCandidate(
            relation="inv",
            candidate="(>= __inv_0 0)",
            rule_id=2,
            rule="inv_step",
            pre_state=pre_state,
            post_state="__inv_0 = -1, __inv_1 = 3",
            full_model="[__pyhorn_r2_0_x = -1, __pyhorn_r2_0_n = 3]",
        )

    def test_format_includes_relation(self):
        rc = self._make_rc(pre_state="__inv_0 = 5, __inv_1 = 3")
        text = _format_removed_candidate(rc)
        assert "inv" in text

    def test_format_includes_candidate(self):
        rc = self._make_rc(pre_state="__inv_0 = 5, __inv_1 = 3")
        text = _format_removed_candidate(rc)
        assert "(>= __inv_0 0)" in text

    def test_format_includes_post_state(self):
        rc = self._make_rc(pre_state="__inv_0 = 5, __inv_1 = 3")
        text = _format_removed_candidate(rc)
        assert "__inv_0 = -1" in text

    def test_format_includes_pre_state_when_set(self):
        rc = self._make_rc(pre_state="__inv_0 = 5, __inv_1 = 3")
        text = _format_removed_candidate(rc)
        assert "__inv_0 = 5" in text

    def test_format_shows_fact_label_when_pre_none(self):
        rc = self._make_rc(pre_state=None)
        text = _format_removed_candidate(rc)
        assert "fact" in text.lower()

    def test_format_includes_rule_id(self):
        rc = self._make_rc(pre_state=None)
        text = _format_removed_candidate(rc)
        assert "r2" in text


# ---------------------------------------------------------------------------
# CLI integration: --debug prints removed candidates to stderr
# ---------------------------------------------------------------------------


class TestCliDebugPrintsRemovedCandidates:

    def test_debug_flag_prints_dropped_to_stderr(self, capsys):
        ret = main([
            "--seed-houdini", "--debug",
            str(EXAMPLES / "counter_safe.smt2"),
        ])
        assert ret == 0
        stderr = capsys.readouterr().err
        # At least one candidate is removed for counter_safe
        assert "dropped" in stderr.lower()

    def test_no_debug_no_dropped_output(self, capsys):
        ret = main([
            "--seed-houdini",
            str(EXAMPLES / "counter_safe.smt2"),
        ])
        assert ret == 0
        stderr = capsys.readouterr().err
        assert "dropped" not in stderr.lower()

    def test_json_includes_removed_candidates_key(self, capsys):
        ret = main([
            "--seed-houdini", "--json",
            str(EXAMPLES / "counter_safe.smt2"),
        ])
        assert ret == 0
        payload = json.loads(capsys.readouterr().out)
        assert "removed_candidates" in payload
        assert isinstance(payload["removed_candidates"], list)

    def test_json_removed_candidates_have_required_fields(self, capsys):
        ret = main([
            "--seed-houdini", "--json",
            str(EXAMPLES / "counter_safe.smt2"),
        ])
        assert ret == 0
        payload = json.loads(capsys.readouterr().out)
        for rc in payload["removed_candidates"]:
            assert "relation" in rc
            assert "candidate" in rc
            assert "rule_id" in rc
            assert "rule" in rc
            assert "pre_state" in rc   # may be null
            assert "post_state" in rc
            assert "full_model" in rc

    def test_json_removed_candidates_non_empty_for_counter_safe(self, capsys):
        main(["--seed-houdini", "--json", str(EXAMPLES / "counter_safe.smt2")])
        payload = json.loads(capsys.readouterr().out)
        assert len(payload["removed_candidates"]) > 0
