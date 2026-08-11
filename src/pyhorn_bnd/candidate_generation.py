"""Neutral extension API for invariant-candidate generators.

Candidate generators are untrusted proposal mechanisms.  They may be
syntactic, trace-template based, statistical, or learned.  Soundness is
provided only by MultiHoudini and the fresh CHC certification pass.
"""

from __future__ import annotations

from collections.abc import Mapping
from dataclasses import dataclass, field
from typing import Protocol, runtime_checkable

import z3

from .seedminer import CandidateMap, VariableMap


@dataclass(frozen=True)
class CandidateBatch:
    """A named batch of candidate formulas over one canonical variable map."""

    generator_id: str
    variables: VariableMap
    candidates: CandidateMap
    metadata: Mapping[str, object] = field(default_factory=dict)

    def __post_init__(self) -> None:
        if not self.generator_id:
            raise ValueError("generator_id must be nonempty")
        variable_ids = {relation.get_id() for relation in self.variables}
        missing = [
            relation
            for relation in self.candidates
            if relation.get_id() not in variable_ids
        ]
        if missing:
            names = ", ".join(sorted(str(item.name()) for item in missing))
            raise ValueError(f"candidate batch contains unknown relations: {names}")

    @property
    def candidate_count(self) -> int:
        return sum(len(items) for items in self.candidates.values())


@runtime_checkable
class CandidateGenerator(Protocol):
    """Protocol reserved for current and future candidate proposal engines.

    Implementations may use deterministic templates, external tools, or
    machine-learning models.  Generated formulas must use the supplied
    canonical variables.  The protocol does not grant proof authority.
    """

    generator_id: str

    def generate(self) -> CandidateBatch:
        """Return one finite batch of candidate formulas."""


def merge_candidate_batches(
    variables: VariableMap,
    *batches: CandidateBatch,
) -> CandidateMap:
    """Merge batches after checking that their canonical variables agree."""

    merged: CandidateMap = {}
    batch_variables = [
        {relation.get_id(): canonical for relation, canonical in batch.variables.items()}
        for batch in batches
    ]
    batch_candidates = [
        {relation.get_id(): items for relation, items in batch.candidates.items()}
        for batch in batches
    ]
    for relation, canonical in variables.items():
        relation_id = relation.get_id()
        bucket: dict[str, z3.BoolRef] = {}
        for batch, variable_map, candidate_map in zip(
            batches, batch_variables, batch_candidates, strict=True
        ):
            batch_canonical = variable_map.get(relation_id)
            if batch_canonical is None:
                continue
            if len(batch_canonical) != len(canonical) or any(
                not left.eq(right)
                for left, right in zip(batch_canonical, canonical, strict=True)
            ):
                raise ValueError(
                    "candidate batch uses incompatible canonical variables for "
                    f"{relation.name()}"
                )
            for candidate in candidate_map.get(relation_id, ()):
                normalized = z3.simplify(candidate)
                if not z3.is_bool(normalized):
                    raise ValueError(
                        f"candidate from {batch.generator_id} is not Boolean: "
                        f"{normalized}"
                    )
                bucket.setdefault(normalized.sexpr(), normalized)
        merged[relation] = tuple(
            expression
            for _, expression in sorted(bucket.items(), key=lambda item: item[0])
        )
    return merged
