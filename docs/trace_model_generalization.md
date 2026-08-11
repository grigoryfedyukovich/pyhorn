# Candidate synthesis from bounded trace models

## Status

Implemented in PyHorn 0.0.17 as `--trace-houdini`.

The implementation is a sound **generate-and-prove** pipeline:

1. Enumerate connected CHC prefixes from `ENTRY` breadth-first.
2. Build the same positional SSA formulas used by bounded exploration.
3. Ask Z3 for one or more concrete destination-state models per prefix.
4. Instantiate the fixed trace-template registry over the observed states.
5. Merge those hypotheses with ordinary syntactic SeedMiner candidates.
6. Run MultiHoudini and independently certify every CHC.

Trace samples are not proofs. Incomplete or unrepresentative sampling may lead
to weak candidates and `unknown`; it cannot justify a false `Success`.

The exact, exhaustive template language is specified in
[`trace_candidate_templates.md`](trace_candidate_templates.md) and is available
programmatically through `trace_template_specifications()`.

## CLI

```bash
pyhorn-expl \
  --trace-houdini \
  --trace-depth 8 \
  --trace-limit 1000 \
  --trace-models-per-prefix 2 \
  --trace-samples-per-predicate 64 \
  --trace-candidates-per-predicate 256 \
  input.smt2
```

The strategy is staged:

- ordinary SeedMiner + MultiHoudini runs first;
- if it proves the input, trace sampling is skipped;
- otherwise, trace candidates are generated and the combined set is checked.

This prevents speculative trace candidates from turning an existing
Seed-Houdini proof into `unknown`.

To inspect the supported template registry without supplying an input file:

```bash
pyhorn-expl --list-trace-templates
pyhorn-expl --list-trace-templates --json
```

## Prefix and model generation

A prefix is a connected rule sequence starting at `ENTRY` and ending at any
non-query predicate. Query rules may be checked while traversing, but have no
destination state to sample.

For every prefix, `VerificationConditionBuilder.build_prefix()` constructs the
same deterministic SSA rule instances as bounded exploration. A fresh sampling
solver asserts the complete prefix. If it is satisfiable, the final predicate's
SSA state variables are evaluated with model completion.

To obtain more than one state from a nondeterministic prefix, the sampler adds a
blocking clause:

```text
state_0 != value_0 OR ... OR state_n != value_n
```

and asks for another model, up to the configured per-prefix limit.

The following limits bound time and memory:

- maximum prefix depth;
- maximum checked prefixes;
- maximum models per prefix;
- maximum retained samples per predicate;
- maximum generated candidates per predicate.

## Exact template boundary

The implementation currently has 15 stable template families:

```text
boolean.always-true
boolean.always-false
numeric.constant
numeric.lower-bound
numeric.upper-bound
integer.congruence
numeric.affine-equality
string.constant
string.common-prefix
string.common-suffix
string.observed-alphabet-closure
string.equality
string.prefix-relation
string.suffix-relation
string.concatenation
```

The concise names above are not substitutes for the exact rules. Formula
schemas, supported feature types, coefficient/modulus limits, orientation,
arity restrictions, and emission conditions are defined in
[`trace_candidate_templates.md`](trace_candidate_templates.md).

Every `TraceCandidateObservation` records both:

- `template_id`, the stable family identifier;
- `kind`, an instance-specific diagnostic label.

## Why positive traces help Houdini

SeedMiner sees formulas already present in CHCs. It cannot necessarily invent
the abstraction needed to exclude a bad state. For example:

```text
inv("")
inv(s) -> inv(s ++ "aa")
inv(s) and len(s) = 3 -> false
```

The syntax exposes `len(s) != 3`, which is not inductive. Bounded models expose
lengths `0, 2, 4, 6, ...`; the congruence template proposes
`len(s) mod 2 = 0`, and MultiHoudini proves it.

Similarly, models for the affine example lie on the plane `y = 2*x`, allowing
exact rational nullspace generalization even when syntactic candidates are
insufficient.

## Soundness

The trace miner is heuristic. Soundness comes from MultiHoudini:

- fact clauses prove initiation;
- transition clauses prove candidate preservation;
- query clauses prove error exclusion;
- a fresh certification solver reconstructs and validates every final CHC.

If any required check is satisfiable or unknown, the result is `unknown`.

## Current evaluation

The original pyhorn-bounded-explorer 0.0.17 branch reported, on an external
350-file FreqHorn `bench_horn` corpus (excluding `sn_4096`/`sn_8192`, not
bundled in this repository) at depth 4, at most 50 prefixes, one model per
prefix, a 300 ms per-check timeout, and Z3 seed 1: Seed-Houdini proved 114
and trace-enhanced Houdini proved 160 (46 additional successes, no
regressions); the string-length parity benchmark changed from `unknown` to
`Success`; tested known-counterexample inputs remained `unknown`, never
falsely `Success`. Those figures are from that branch's own environment and
have not been independently reproduced here, since the external corpus
isn't part of this repository.

On this repository's own bundled `examples/bench_horn/` (10 files, the same
configuration above), trace-enhanced Houdini proves one additional benchmark
over plain Seed-Houdini (`03_mixed_bool_int_mod_ite.smt2`) with no
regressions -- consistent with, though far smaller than, the original
result. On the dedicated `examples/string_length_literature/` and
`examples/trace_houdini/` suites, the two benchmarks purpose-built to need a
template plain syntactic mining can't produce
(`append_two_parity_safe.smt2`'s modular-length invariant,
`count_by_2_modular_safe.smt2`'s congruence invariant) move from `unknown`
under plain Seed-Houdini to `Success` under `--trace-houdini`, and
`abdu_02_affine_safe.smt2`'s affine invariant likewise moves from `unknown`
to `Success`. `integer_affine_safe.smt2` is proved by both -- it's included
in the suite as a baseline case where syntactic mining is already
sufficient, not one requiring trace generalization.

Reproduce either of the above with:

```bash
PYTHONPATH=src python3 tools/audit_trace_generalization.py \
  examples/bench_horn --depth 4 --limit 50 --timeout-ms 300 --json
```

substituting the path to the external 350-file corpus, or any other
directory of `.smt2` files, for `examples/bench_horn`.

## Future learned candidate generators

PyHorn does not commit to a particular counterexample-learning framework. The
candidate proposal layer now exposes a neutral `CandidateGenerator` /
`CandidateBatch` API documented in
[`candidate_generator_api.md`](candidate_generator_api.md).

A future machine-learning component may rank templates, choose sampling
budgets, or propose new formulas. Such output remains untrusted and must pass
the same MultiHoudini filtering and fresh certification checks.
