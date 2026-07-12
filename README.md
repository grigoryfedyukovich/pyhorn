# Standalone Python bounded CHC explorer

This repository provides a standalone Python 3/Z3Py bounded trace explorer
for linear constrained Horn clauses. It has no external C++ implementation,
CMake build, machine-learning component, or benchmark-suite dependency.

The explorer:

1. parses a linear constrained Horn-clause system with Z3;
2. normalizes every clause into a typed `HornProgram` / `HornRule` database;
3. enumerates all ENTRY-to-error traces exhaustively in increasing length;
4. converts each trace to an SSA verification condition using native Z3 ASTs;
5. caches deterministic `(rule_id, step_index)` SSA instances across traces;
6. optionally dumps every constructed trace SSA to its own replayable SMT-LIB2 file;
7. checks traces through a pool of incremental `z3.Solver` contexts, reusing the
   longest common SAT prefix via `pop()` / `push()`; and
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

## Important options

- `--from N`: first trace length, default `1`;
- `--upto N`: maximum trace length, default `10000`;
- `--to MS`: timeout for each incremental Z3 check, default `1000` ms;
- `--debug`: print normalized rules and per-depth statistics;
- `--json`: produce machine-readable output;
- `--model`: print a counterexample model;
- `--dump-vc FILE`: save only the decisive SAT/unknown trace VC as SMT-LIB;
- `--dump-ssa DIR`: save every constructed trace SSA as a separate SMT-LIB2
  file in `DIR` (alias: `--dump-ssa-dir`). The directory must be empty or
  nonexistent; files are numbered in exploration order and include trace depth
  in their names. Each SSA step appears as a separate `(assert ...)`;
- `--fresh-solvers`: disable cross-trace solver reuse for comparison;
- `--solver-reuse-min-ratio R`: reuse the best solver only when its common
  prefix is longer than `R * trace_length`; the default is `1/3`, matching the
  Aeval `SMTUtils::isSatIncrem` heuristic;
- `--max-solvers N`: cap retained solver contexts and recycle the least recently
  used one when necessary. The default `0` leaves the pool unbounded;
- `--skip-elim`: retain rules outside the semantics-preserving
  ENTRY-to-query graph slice.

Exit codes are `0` for bounded/complete safety, `1` for a counterexample, `2`
for Z3 `unknown`, and `3` for input or usage errors.

### Dump every constructed SSA

```bash
python3 bounded_explorer.py \
  --upto 20 \
  --dump-ssa ssa-dumps \
  examples/assert_syntax.smt2
```

The output directory contains files such as:

```text
ssa_000001_depth_000002.smt2
ssa_000002_depth_000003.smt2
ssa_000003_depth_000004.smt2
```

A file is written immediately after construction and before solving. It starts
with comments identifying the rule sequence, followed by one assertion per SSA
step and a final `(check-sat)`, so it can be inspected or replayed directly.

## Incremental solver-pool reuse

Each retained solver context represents a rule prefix whose SSA constraints have
already been proved satisfiable. For a new trace, the explorer:

1. compares its rule sequence with every retained context;
2. chooses the longest common prefix;
3. reuses that context when the prefix passes the configured ratio threshold;
4. calls `pop()` once per divergent old step;
5. calls `push()`, `add()`, and `check()` for each new suffix step.

A newly unsatisfiable or `unknown` step is popped immediately, so the stored
context always remains a known-SAT prefix. If no context is a useful fit, a new
solver is created. With `--max-solvers`, the least recently used context is
replaced instead.

The `--debug` output reports solver contexts created, reused prefix steps,
pushes, pops, checks, and SSA-cache hits/misses. The same counters are included
in `--json` output.

## Repository layout

```text
bounded_explorer.py       direct launcher
src/pyhorn_bnd/           parser, normalization, VC storage, explorer, CLI
examples/                 small examples of both accepted syntaxes
tests/                    standalone regression tests
```

## Tests

```bash
python3 -m pip install pytest ruff
python3 -m pytest -q
python3 -m ruff check .
```
