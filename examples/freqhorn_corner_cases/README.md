# Original FreqHorn corner cases

These files are copied from the original FreqHorn benchmark suites and are kept
small enough for parser, SeedMiner, MultiHoudini, and soundness regressions.

| File | Original suite | Corner case |
|---|---|---|
| `missing_explicit_query.smt2` | `bench_horn_multiple` | A terminal nullary `fail` relation without an explicit `(query fail)` command |
| `numeric_equality_bounds.smt2` | `bench_horn` | Equalities whose useful invariant consequences are one-sided numeric bounds |
| `repeated_query_arguments.smt2` | `bench_horn` | Query source relation applied to repeated arguments; requires preserving the complete bad-state pattern |
| `quantified_array_invariant.smt2` | `bench_horn` | Rule-local query index becomes a universally quantified array invariant |
| `quantified_model_fallback.smt2` | `bench_horn` | Z3 may not evaluate a quantified candidate to a concrete Boolean in a combined countermodel |
| `unsafe_quantified_array.smt2` | `bench_horn_cex` | Quantified/array unsafe case; Seed-Houdini must never report `Success` |

The files intentionally preserve the source syntax and organization of the
original corpus.
