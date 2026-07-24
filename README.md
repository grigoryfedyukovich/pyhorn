# PyHorn: bounded CHC exploration and seed-Houdini

This repository provides Python 3/Z3Py analysis for linear constrained Horn
clauses. It includes exhaustive bounded trace exploration and a syntactic
SeedMiner followed by multi-predicate Houdini filtering.

The bounded explorer:

1. parses a linear constrained Horn-clause system with Z3;
2. normalizes every clause into a typed `HornProgram` / `HornRule` database;
3. enumerates all ENTRY-to-error traces exhaustively in increasing length;
4. converts each trace to an SSA verification condition using native Z3 ASTs;
5. caches deterministic `(rule_id, step_index)` SSA instances in a bounded LRU cache;
6. optionally dumps every checked trace as a compact, replayable
   `bnd/expl`-compatible SMT-LIB2 unrolling;
7. checks traces either with a cross-trace incremental solver pool or with the
   original fresh-solver-per-trace baseline; and
8. caches infeasible rule prefixes to prune every longer trace that begins with
   one of them.

## Supported input formats

Both common CHC encodings are supported.

### Z3 fixedpoint command syntax

```smt2
(declare-var x Int)
(declare-rel inv (Int))
(declare-rel fail ())
(rule (inv 0))
(rule (=> (and (inv x) (< x 2)) (inv (+ x 1))))
(rule (=> (and (inv x) (>= x 2)) fail))
(query fail)
```

### Pure SMT-LIB HORN assertions

```smt2
(set-logic HORN)
(declare-fun inv (Int) Bool)
(assert (inv 0))
(assert
  (forall ((x Int))
    (=> (and (inv x) (< x 2))
        (inv (+ x 1)))))
(assert
  (forall ((x Int))
    (=> (and (inv x) (>= x 2))
        false)))
(check-sat)
```

For pure SMT-LIB input, a clause ending in `false` is treated as an error
clause. An interpreted safety head is also supported. For example,
`(assert (forall ((x Int)) (=> (inv x) (<= x 1))))` is checked by exploring
states satisfying `inv(x)` and the negation of the asserted property.

The supported fragment is **linear CHC**: a rule body may contain at most one
positive relation application. Nonlinear clauses are rejected with an explicit
diagnostic. Integer, real, array, bit-vector, Boolean, and retained nested
quantifier constraints are represented directly by Z3 expressions.

## Original FreqHorn benchmark coverage

The parser and type checker have been run over all three original FreqHorn
benchmark suites:

| Suite | Files | Normalized CHCs |
|---|---:|---:|
| `bench_horn` | 352 | 1,056 |
| `bench_horn_cex` | 79 | 435 |
| `bench_horn_multiple` | 176 | 953 |
| **Total** | **607** | **2,444** |

All files parse successfully. Legacy files that omit `(query fail)` are accepted
only when there is exactly one terminal nullary relation; ambiguous implicit
queries are rejected.

The corpus exercises integer, real, Boolean, array, and bit-vector expressions;
constants and expressions in relation arguments; `ite`, arithmetic, `div`,
`mod`, nonlinear multiplication, `select`, `store`, constant arrays,
`define-fun`, `distinct`, annotations, and quantified constraints.

Ten theory/operator examples live in `examples/bench_horn/`. Additional
benchmark-driven edge cases live in `examples/freqhorn_corner_cases/`. The full
audit, solve counts, fixes, and remaining candidate-language gaps are documented
in [`docs/freqhorn_benchmark_audit.md`](docs/freqhorn_benchmark_audit.md).

## Installation

```bash
python3 -m pip install .
```

This installs both command names:

```bash
chc-bounded-explorer --upto 20 input.smt2
pyhorn-expl --upto 20 input.smt2
```

It can also be run directly without installation:

```bash
python3 bounded_explorer.py --upto 20 examples/assert_syntax.smt2
```

## SeedMiner and MultiHoudini

Run the complete candidate-mining and invariant-filtering pipeline with:

```bash
pyhorn-expl --seed-houdini input.smt2
```

The default human-readable output is deliberately just one of:

```text
Success
```

or:

```text
unknown
```

`Success` is reported only when the conjunction of candidates retained for each
predicate makes **every** normalized fact, transition, and query CHC valid.
`unknown` means either that a query remains satisfiable under the retained
candidates or that Z3 returned `unknown`; it is not a claim that the input is
unsafe.

Print the retained predicate annotations and diagnostics with:

```bash
pyhorn-expl \
  --seed-houdini \
  --print-invariants \
  --debug \
  input.smt2
```

Use `--json` for candidate, filtering, and failure statistics.

### Candidate mining

SeedMiner creates canonical typed variables for every non-query predicate and
observes the normalized Z3 parse tree of every CHC. It mines:

- Boolean subtrees, splitting conjunctions while preserving disjunctions;
- complete negated query bad-state patterns;
- repeated, constant, and nontrivial relation-argument structure;
- both one-sided arithmetic bounds implied by numeric equality;
- universally closed query candidates when bad-state witnesses are rule-local;
- candidates transferred across pure predicate-renaming/permutation rules.

Candidates remain native Z3 ASTs, including arrays, bit-vectors, Booleans,
arithmetic, `select`, `store`, and quantifiers. Every accepted candidate is
predicate-local; noncanonical free variables are rejected.

This remains a syntactic candidate language. It does not yet synthesize general
affine combinations, modular/path-sensitive invariants, polynomial templates,
or the original implementation's full array range/access grammar. These limits
reduce completeness but cannot make a certified answer unsound.

### MultiHoudini filtering

MultiHoudini accepts one candidate set per predicate. It lazily creates one
persistent filtering solver for each relevant non-query CHC. Source candidates
are guarded by assumption literals. The active destination violation is added
in a balanced temporary scope:

```text
rule body
and active source candidates
and some active destination candidate is false
```

A satisfiable check removes every destination candidate falsified by the model.
If Z3 does not concretely evaluate a quantified candidate, PyHorn checks active
destination candidates individually under the same source assumptions. A Z3
`unknown` or unattributable SAT result produces conservative `unknown`, not an
internal failure.

After filtering reaches a fixed point, **every original CHC is reconstructed
and checked in a fresh solver**. Query clauses participate in this independent
certification. `Success` is returned only if all certification obligations are
UNSAT.

Focused safe, unsafe, array, multiple-predicate, and original-corpus corner cases
are under `examples/seed_houdini/` and `examples/freqhorn_corner_cases/`.

### Corpus audit

Reproduce a suite run with:

```bash
PYTHONPATH=src python3 tools/check_seed_houdini_corpus.py \
  /path/to/bench_horn \
  --timeout 1000 \
  --random-seed 1
```

With a 1,000 ms per-check timeout and seed 1, version 0.0.11 produced:

| Suite | Success | Unknown | Errors |
|---|---:|---:|---:|
| `bench_horn` | 115 | 237 | 0 |
| `bench_horn_cex` | 0 | 79 | 0 |
| `bench_horn_multiple` | 29 | 147 | 0 |

No known counterexample benchmark was reported as `Success`. Results may vary
slightly with Z3 version and timeout behavior; `unknown` is always conservative.
See [`docs/freqhorn_benchmark_audit.md`](docs/freqhorn_benchmark_audit.md) for
bounded-exploration results and corner-case analysis.

## Solver modes

The default mode is a cross-trace incremental pool retaining at most 16
solver contexts:

```bash
pyhorn-expl --solver-mode pool --max-solvers 16 --upto 20 input.smt2
```

The explicit `--max-solvers 16` above matches the default and is shown to make
the experimental configuration visible. Set another positive value to change
the memory/reuse tradeoff, or use `--max-solvers 0` for an intentionally
unbounded pool.

Each retained solver represents a rule prefix whose SSA constraints have already
been proved satisfiable. For a new trace, the explorer finds the retained solver
with the longest common rule prefix, pops its divergent suffix, and pushes and
checks the new suffix.

The original baseline is available explicitly:

```bash
pyhorn-expl --solver-mode fresh --upto 20 input.smt2
```

`fresh` mode has the following precise behavior:

- creates one new `z3.Solver` for every candidate trace;
- adds SSA constraints monotonically, one trace step at a time;
- calls `check()` after each addition to identify the first infeasible prefix;
- never calls `push()` or `pop()`;
- retains no solver assertions or learned solver state across traces.

Both modes use the same parser, normalized rules, trace order, SSA cache, SMT
dumps, and infeasible-prefix pruning. Therefore, comparing these two commands
isolates the effect of cross-trace solver reuse:

```bash
pyhorn-expl \
  --solver-mode pool \
  --random-seed 1 \
  --upto 100 \
  --json \
  input.smt2 > pool.json

pyhorn-expl \
  --solver-mode fresh \
  --random-seed 1 \
  --upto 100 \
  --json \
  input.smt2 > fresh.json
```

For controlled timing experiments, run each mode several times in separate
processes and compare at least:

- total wall-clock time;
- `solvers_created`;
- `checks`;
- `pushes` and `pops`;
- `common_prefix_steps_reused`;
- SSA cache hits and misses.

In fresh mode, `pushes`, `pops`, and retained `contexts` are always zero, while
`solvers_created` equals the number of traces actually checked.

## Important options

- `--from N`: first trace length, default `1`;
- `--upto N`: maximum trace length, default `10000`;
- `--to MS`: timeout for each Z3 check, default `1000` ms;
- `--debug`: print normalized rules and per-depth statistics;
- `--json`: produce machine-readable output;
- `--model`: print a counterexample model;
- `--seed-houdini`: run SeedMiner, MultiHoudini, and final CHC validation instead
  of bounded trace exploration;
- `--print-invariants`: print retained candidates in `--seed-houdini` mode;
- `--dump-vc FILE`: save only the decisive SAT/unknown trace VC as SMT-LIB;
- `--dump-smt DIR`: save every checked trace as a compact SMT-LIB2 unrolling
  using the original `bnd/expl` filename and file format. Existing directories
  are allowed;
- `--solver-mode {pool,fresh}`: select the solver backend, default `pool`;
- `--solver-reuse-min-ratio R`: in pool mode, reuse the best solver only when
  its common prefix is longer than `R * trace_length`; the default is `1/3`;
- `--max-solvers N`: in pool mode, cap retained solver contexts and reset/reuse
  the least recently used solver when necessary. The default is `16`; `0`
  intentionally disables the limit;
- `--max-ssa-cache-steps N`: cap cached SSA steps and state versions. The
  default is `65536`; `0` intentionally disables the limit;
- `--skip-elim`: retain rules outside the semantics-preserving ENTRY-to-query
  graph slice.

Exit codes are `0` for bounded/complete safety or seed-Houdini `Success`, `1`
for a bounded counterexample, `2` for `unknown`, and `3` for input or usage
errors.

### Dump checked unrollings in `bnd/expl` format

```bash
python3 bounded_explorer.py \
  --upto 10 \
  --dump-smt unrollings \
  examples/bench_horn_multiple/abdu_05.smt2
```

The filename is derived from the input benchmark, bound, trace number, and Z3
result:

```text
abdu_05_k3_unsat.smt2
abdu_05_k4_t1_unsat.smt2
abdu_05_k4_t2_unsat.smt2
...
abdu_05_k10_t8_unsat.smt2
```

The `_tN` component is omitted when a bound has only one candidate trace. When
a bound has multiple candidates, `N` is the one-based position in the complete
trace list generated for that bound, matching the C++ explorer. The final suffix
is `_sat`, `_unsat`, or `_unknown`.

Each file is written after the corresponding Z3 check and has the compact form:

```smt2
; bnd/expl SMT dump
; bound: 3
; result: unsat

(declare-fun __bnd_var_0 () Int)
...
(assert (and ...))
(check-sat)
```

There is exactly one conjunctive `(assert ...)`. State versions use
`__bnd_var_N`, while rule-local symbols use `__loc_var_N`. The internal solver
may use a more explicit cached SSA representation, but the dumped formula is
equisatisfiable and follows the compact C++ convention. Existing files with the
same generated name are replaced; unrelated files in the directory are kept.

The regression suite includes `abdu_05.smt2` and all 36 attached C++ reference
dumps. It checks that the generated filename set is identical and that every
Python dump is logically equivalent to its C++ counterpart.

## Incremental solver-pool reuse

In `pool` mode, the explorer:

1. indexes retained contexts by the first rule of the new trace;
2. chooses the context in that bucket with the longest common prefix;
3. reuses it when the prefix passes the configured ratio threshold;
4. calls `pop()` once per divergent old step;
5. calls `push()`, `add()`, and `check()` for every new suffix step.

A newly unsatisfiable or `unknown` step is popped immediately, so every stored
context remains a known-SAT prefix. If no context is a useful fit, a new solver
is created until the configured limit is reached. The default limit is 16.
After that, the least recently used context is reset and its existing physical
Z3 solver object is reused, bounding retained native solver memory.

The `--debug` output reports the selected solver mode, configured pool limit,
solvers created, recycled contexts, retained contexts, reused prefix steps,
pushes, pops, checks, and SSA-cache size/hits/misses/evictions. The same counters,
`solver_mode`, and `max_contexts` are included in `--json` output.

## Python API

The default API uses the solver pool:

```python
from pyhorn_bnd import BoundedExplorer, parse_chc_file

program = parse_chc_file("input.smt2")
result = BoundedExplorer(
    program, solver_mode="pool", max_solver_contexts=16
).explore(upto=100)
```

Use the baseline backend with:

```python
result = BoundedExplorer(program, solver_mode="fresh").explore(upto=100)
```

The seed-Houdini API is:

```python
from pyhorn_bnd import parse_chc_file, run_seed_houdini

program = parse_chc_file("input.smt2", slice_program=False)
result = run_seed_houdini(program, timeout_ms=1000, random_seed=1)
print(result.status.value)
```

For controlled experiments with explicit candidate sets, use `SeedMiner` and
`MultiHoudini` separately:

```python
from pyhorn_bnd import MultiHoudini, SeedMiner

seeds = SeedMiner(program).mine()
result = MultiHoudini(program, seeds.variables).run(seeds.candidates)
```

## Repository layout

```text
bounded_explorer.py       direct launcher
src/pyhorn_bnd/           parser, SeedMiner, MultiHoudini, VC/explorer, CLI
examples/                 syntax examples and extracted corpus cases
docs/                     implementation, Houdini, and parser specifications
tests/                    standalone and optional corpus regressions
tools/                    parser and seed-Houdini corpus utilities
```


## Version and compatibility

The package exposes its version through:

```python
import pyhorn_bnd
print(pyhorn_bnd.__version__)
```

Version `0.0.11` adds complete original-suite parsing, benchmark-driven
SeedMiner/Houdini corner-case handling, and fresh final CHC certification.
Version `0.0.10` removed pre-1.0 compatibility aliases from the Python API
and CLI. Use `solver_mode="fresh"`, `smt_dump_dir=...`, `solver_backend`, and
`--dump-smt` directly.

The implementation contract is documented in
[`docs/implementation_spec.md`](docs/implementation_spec.md). Detailed Houdini
solver semantics are in
[`docs/houdini_incremental_solver_spec.md`](docs/houdini_incremental_solver_spec.md).

## Tests

```bash
python3 -m pip install pytest ruff
python3 -m pytest -q
python3 -m ruff check .
```

To run the complete external corpus regression:

```bash
PYHORN_BENCH_HORN_DIR=/path/to/bench_horn \
  python3 -m pytest -q tests/test_bench_horn_corpus.py
```

The ordinary test suite does not depend on the external corpus; it uses the ten
theory/operator cases in `examples/bench_horn/`, focused Seed-Houdini examples,
and the original benchmark edge cases in `examples/freqhorn_corner_cases/`.
