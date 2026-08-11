from __future__ import annotations

import json
from pathlib import Path

import z3

from pyhorn_bnd import (
    CandidateBatch,
    CandidateGenerator,
    SeedMiner,
    TraceCandidateMiner,
    TraceTemplateId,
    merge_candidate_batches,
    parse_chc_file,
    trace_template_specifications,
)
from pyhorn_bnd.cli import main

ROOT = Path(__file__).resolve().parents[1]
TRACE_EXAMPLES = ROOT / "examples" / "trace_houdini"
LENGTH_EXAMPLES = ROOT / "examples" / "string_length_literature"


EXPECTED_TEMPLATE_IDS = (
    "boolean.always-true",
    "boolean.always-false",
    "numeric.constant",
    "numeric.lower-bound",
    "numeric.upper-bound",
    "integer.congruence",
    "numeric.affine-equality",
    "string.constant",
    "string.common-prefix",
    "string.common-suffix",
    "string.observed-alphabet-closure",
    "string.equality",
    "string.prefix-relation",
    "string.suffix-relation",
    "string.concatenation",
)


def _relation(program, name: str) -> z3.FuncDeclRef:
    return next(
        relation for relation in program.relations if str(relation.name()) == name
    )


def _equivalent(left: z3.BoolRef, right: z3.BoolRef) -> bool:
    solver = z3.Solver()
    solver.add(z3.Xor(left, right))
    return solver.check() == z3.unsat


def _registry_payload() -> list[dict[str, object]]:
    return [
        {
            "id": item.template_id.value,
            "domain": item.domain,
            "formula_schema": item.formula_schema,
            "applicable_features": list(item.applicable_features),
            "emission_condition": item.emission_condition,
        }
        for item in trace_template_specifications()
    ]


def test_trace_template_registry_is_complete_stable_and_snapshotted() -> None:
    specifications = trace_template_specifications()
    assert tuple(item.template_id.value for item in specifications) == (
        EXPECTED_TEMPLATE_IDS
    )
    assert len({item.template_id for item in specifications}) == len(specifications)

    snapshot = json.loads(
        (ROOT / "docs" / "trace_candidate_templates.json").read_text(
            encoding="utf-8"
        )
    )
    assert snapshot == _registry_payload()


def test_trace_template_registry_cli_needs_no_input_file(capsys) -> None:
    assert main(["--list-trace-templates", "--json"]) == 0
    assert json.loads(capsys.readouterr().out) == _registry_payload()


def test_observations_report_stable_template_ids() -> None:
    program = parse_chc_file(
        TRACE_EXAMPLES / "integer_affine_safe.smt2", slice_program=False
    )
    seeds = SeedMiner(program).mine()
    result = TraceCandidateMiner(
        program,
        seeds.variables,
        max_depth=6,
        models_per_prefix=1,
        timeout_ms=5_000,
    ).mine()
    assert TraceTemplateId.AFFINE_EQUALITY in {
        item.template_id for item in result.observations
    }

    program = parse_chc_file(
        LENGTH_EXAMPLES / "append_two_parity_safe.smt2", slice_program=False
    )
    seeds = SeedMiner(program).mine()
    result = TraceCandidateMiner(
        program,
        seeds.variables,
        max_depth=6,
        models_per_prefix=1,
        timeout_ms=5_000,
    ).mine()
    assert TraceTemplateId.INTEGER_CONGRUENCE in {
        item.template_id for item in result.observations
    }


def test_prefix_and_suffix_relations_are_generated_in_both_orientations(
    tmp_path: Path,
) -> None:
    source = tmp_path / "ordered_string_relations.smt2"
    source.write_text(
        """
        (declare-var a String)
        (declare-var b String)
        (declare-rel inv (String String))
        (declare-rel fail ())
        (rule (inv "a" "ab"))
        (rule (=> (inv a b) (inv (str.++ "x" a) (str.++ "x" b))))
        (rule (=> (and (inv a b) (not (= a a))) fail))
        (query fail)
        """,
        encoding="utf-8",
    )
    program = parse_chc_file(source, slice_program=False)
    seeds = SeedMiner(program).mine()
    result = TraceCandidateMiner(
        program,
        seeds.variables,
        max_depth=4,
        models_per_prefix=1,
        timeout_ms=5_000,
    ).mine()
    inv = _relation(program, "inv")
    left, right = seeds.variables[inv]

    assert any(
        item.template_id is TraceTemplateId.STRING_PREFIX_RELATION
        and _equivalent(item.candidate, z3.PrefixOf(left, right))
        for item in result.observations
    )


def test_candidate_generator_extension_api_merges_current_generators() -> None:
    program = parse_chc_file(
        TRACE_EXAMPLES / "integer_affine_safe.smt2", slice_program=False
    )
    seed_generator = SeedMiner(program)
    assert isinstance(seed_generator, CandidateGenerator)
    seed_batch = seed_generator.generate()
    assert isinstance(seed_batch, CandidateBatch)
    assert seed_batch.generator_id == "seedminer"

    trace_generator = TraceCandidateMiner(
        program,
        seed_batch.variables,
        max_depth=5,
        models_per_prefix=1,
        timeout_ms=5_000,
    )
    assert isinstance(trace_generator, CandidateGenerator)
    trace_batch = trace_generator.generate()
    assert trace_batch.generator_id == "trace-templates"

    merged = merge_candidate_batches(
        seed_batch.variables,
        seed_batch,
        trace_batch,
    )
    assert sum(len(items) for items in merged.values()) >= max(
        seed_batch.candidate_count,
        trace_batch.candidate_count,
    )
