# SeedMiner and MultiHoudini design

## Pipeline

`run_seed_houdini(program)` performs three steps:

1. `SeedMiner` walks every normalized CHC and creates predicate-local candidate
   formulas over canonical typed variables.
2. `MultiHoudini` incrementally removes candidates falsified by CHC
   countermodels.
3. Every normalized fact, transition, and query is validated under the final
   conjunctions. The result is `success` only if all checks are unsatisfiable.

The pipeline is sound but intentionally incomplete. Failure to synthesize a
sufficient invariant is reported as `unknown`.

## Seed representation

For a predicate `p(S0, ..., Sn)`, SeedMiner creates canonical constants:

```text
__inv_p_0 : S0
...
__inv_p_n : Sn
```

Names are chosen deterministically and made collision-free with respect to the
input program. Candidate formulas are ordinary `z3.BoolRef` values over these
constants.

For each CHC, SeedMiner observes:

- Boolean subtrees in the constraint body;
- the negated non-recursive query condition;
- source and destination relation arguments.

Direct relation arguments are substituted with canonical predicate variables.
A projected candidate is retained only when all of its free constants are
canonical variables of that one predicate. Conjunctions are split into
individual seeds, while disjunctions and negations remain intact.

## MultiHoudini rule check

For each rule, one persistent solver contains the rule body and guarded source
candidates:

```text
source_guard_i => source_candidate_i(source arguments)
```

At each filtering step, the solver checks the active source guards together
with:

```text
or(not destination_candidate_j(destination arguments))
```

If the result is SAT, every destination candidate false in the model is removed.
If it is UNSAT, the rule preserves all currently active destination candidates.
The process repeats until a complete pass removes nothing.

Query clauses do not have destination candidates and therefore do not weaken the
candidate sets. They are checked during final validation:

```text
rule body and active source candidates
```

A satisfiable query check causes the overall result to be `unknown`.

## Result interpretation

- `success`: the retained conjunctions validate all normalized CHCs.
- `unknown`: the candidate language was insufficient, a query remains
  satisfiable, or Z3 returned `unknown`.

`unknown` does not distinguish a genuinely unsafe system from a safe system that
needs stronger candidates.

## Corpus regression

SeedMiner is exercised by the optional 352-file external corpus test:

```bash
PYHORN_BENCH_HORN_DIR=/path/to/bench_horn \
  python3 -m pytest -q tests/test_bench_horn_corpus.py
```

The complete pipeline can be measured independently:

```bash
PYTHONPATH=src python3 tools/check_seed_houdini_corpus.py \
  /path/to/bench_horn --timeout 1000 --random-seed 1
```

The initial Z3 4.16.0 baseline is 80 successes, 272 unknown results, and no
parser/miner errors.

## Incremental-solver safety details

Temporary destination-violation assertions are installed under `push()` and
removed in a `finally` block. SAT models and `reason_unknown()` are captured
before the scope is restored. Source candidates are activated exclusively by
assumption literals, so arbitrary candidate deletion does not require stack
reconstruction.

The complete solver lifecycle, correctness conditions, backend comparison, and
performance experiment design are specified in
[`houdini_incremental_solver_spec.md`](houdini_incremental_solver_spec.md).
