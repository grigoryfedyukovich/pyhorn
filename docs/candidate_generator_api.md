# Candidate-generator extension API

PyHorn intentionally separates **candidate proposal** from **proof**.
`SeedMiner` (syntactic mining) and `TraceCandidateMiner` (trace templates,
`--trace-houdini`) both implement this extension API today. Future
statistical or machine-learning components can use the same neutral API
without changing MultiHoudini or the certification boundary.

This codebase also has two other candidate sources -- user-supplied
`--cands` files (see `cands.py`) and `--mut` candidate mutation (see
`seedminer.mutate_candidates`) -- that predate this API and are merged by
`cands.merge_candidate_maps` instead. They don't need to conform to
`CandidateGenerator` to be sound (nothing in this codebase is trusted
without MultiHoudini + certification either way), but adapting them to the
same protocol, so all candidate sources go through one merge path, is a
natural follow-up; see the migration notes in this repository's history for
context.

No machine-learning runtime or model is included in PyHorn.

## Protocol

```python
from pyhorn_bnd import CandidateBatch, CandidateGenerator

class MyGenerator:
    generator_id = "example.learned-generator"

    def generate(self) -> CandidateBatch:
        ...
```

`CandidateGenerator` requires:

- a stable nonempty `generator_id`;
- `generate() -> CandidateBatch`.

A `CandidateBatch` contains:

- the generator identifier;
- the canonical `VariableMap` used by SeedMiner and MultiHoudini;
- a finite `CandidateMap` of Boolean Z3 formulas;
- optional diagnostic metadata.

## Merge contract

```python
from pyhorn_bnd import merge_candidate_batches

combined = merge_candidate_batches(
    variables,
    syntax_batch,
    trace_batch,
    learned_batch,
)
```

Merging:

1. verifies that every batch uses the same canonical variables for each
   predicate;
2. rejects non-Boolean candidates;
3. simplifies formulas with Z3;
4. deduplicates them by SMT representation;
5. returns a normal `CandidateMap` consumable by `MultiHoudini`.

## Proof boundary

A generator is never trusted. A learned score, classifier, neural model,
language model, graph model, or external synthesis tool may only propose
formulas. PyHorn reports `Success` only after:

1. MultiHoudini filters the merged candidate set;
2. every original CHC is reconstructed and checked with fresh certification
   solvers.

This allows future machine-learning work to focus on proposal quality,
ranking, batching, or resource allocation while preserving the same soundness
contract.

## Intended future integration points

The API leaves room for, without committing to a particular method:

- ranking existing syntactic and trace templates;
- predicting useful template families or parameter ranges;
- proposing new Z3 formulas from CHC graph/AST representations;
- selecting trace depths and model-diversification policies;
- learning predicate-specific embeddings;
- combining external generators through `CandidateBatch`.

Any future generator should record its configuration and provenance in
`CandidateBatch.metadata` so experiments remain reproducible.
