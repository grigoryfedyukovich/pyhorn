# Standalone Python bounded CHC explorer

This repository provides a standalone Python 3/Z3Py bounded trace explorer for
linear constrained Horn clauses.

The explorer:

1. parses a linear constrained Horn-clause system with Z3;
2. normalizes every clause into a typed `HornProgram` / `HornRule` database;
3. enumerates all ENTRY-to-error traces exhaustively in increasing length;
4. converts each trace to an SSA verification condition using native Z3 ASTs;
5. caches deterministic `(rule_id, step_index)` SSA instances across traces;
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

## `bench_horn` parser coverage

The parser has been run over the complete 352-file `bench_horn` corpus. All
files parse and normalize successfully. Every corpus file has the same linear
three-rule organization: one fact, one self-loop transition, and one transition
to a nullary error relation.

The corpus exercises:

- integer-only, Boolean-only, mixed Boolean/integer, and integer-array state;
- constants and expressions directly in relation arguments;
- `and`, `or`, `not`, comparisons, `ite`, `+`, `-`, `*`, `/`, `div`, and `mod`;
- array `select`, `store`, and constant-array syntax;
- `define-fun`, `distinct`, and query options such as
  `:print-certificate true`.

Ten small extracted cases live in `examples/bench_horn/` and are part of the
default regression suite. A detailed corpus inventory and reproduction commands
are in [`docs/bench_horn_parser_coverage.md`](docs/bench_horn_parser_coverage.md).

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

`--fresh-solvers` is retained as an alias for `--solver-mode fresh`.

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
- `--dump-vc FILE`: save only the decisive SAT/unknown trace VC as SMT-LIB;
- `--dump-smt DIR`: save every checked trace as a compact SMT-LIB2 unrolling
  using the original `bnd/expl` filename and file format. Existing directories
  are allowed. `--dump-ssa` and `--dump-ssa-dir` remain compatibility aliases;
- `--solver-mode {pool,fresh}`: select the solver backend, default `pool`;
- `--fresh-solvers`: alias for `--solver-mode fresh`;
- `--solver-reuse-min-ratio R`: in pool mode, reuse the best solver only when
  its common prefix is longer than `R * trace_length`; the default is `1/3`;
- `--max-solvers N`: in pool mode, cap retained solver contexts and reset/reuse
  the least recently used solver when necessary. The default is `16`; `0`
  intentionally disables the limit;
- `--skip-elim`: retain rules outside the semantics-preserving ENTRY-to-query
  graph slice.

Exit codes are `0` for bounded/complete safety, `1` for a counterexample, `2`
for Z3 `unknown`, and `3` for input or usage errors.

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

1. compares the new trace's rule sequence with every retained context;
2. chooses the context with the longest common prefix;
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
pushes, pops, checks, and SSA-cache hits/misses. The same counters,
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

The legacy constructor option `use_solver_pool=False` is still accepted and maps
to `solver_mode="fresh"`.

## Repository layout

```text
bounded_explorer.py       direct launcher
src/pyhorn_bnd/           parser, normalization, VC storage, explorer, CLI
examples/                 syntax examples and extracted corpus cases
docs/                     parser-coverage notes
tests/                    standalone and optional corpus regressions
tools/                    corpus-validation utility
```

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
representative files checked into `examples/bench_horn/`.
