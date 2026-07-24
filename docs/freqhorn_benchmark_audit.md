# Original FreqHorn benchmark audit

**PyHorn version:** 0.0.11  
**Audit date:** July 18, 2026  
**Z3 seed:** 1  
**Houdini timeout:** 1,000 ms per solver check

## Scope

The audit covers all SMT-LIB files in the three original FreqHorn suites:

| Suite | Files | Normalized CHCs | Intended role |
|---|---:|---:|---|
| `bench_horn` | 352 | 1,056 | Primarily safe, single-predicate benchmarks |
| `bench_horn_cex` | 79 | 435 | Benchmarks with reachable counterexamples |
| `bench_horn_multiple` | 176 | 953 | Multiple-predicate and phase-structured benchmarks |
| **Total** | **607** | **2,444** | |

All 607 files parse, normalize, and pass relation arity/sort validation.

## Benchmark-driven fixes

### 1. Omitted explicit query commands

`bench_horn_multiple/nonlin_multiple_inv_12.smt2` declares a nullary `fail`
relation and a rule reaching it, but has no `(query fail)` command. Earlier
PyHorn versions rejected the file.

PyHorn now conservatively infers a query only when there is exactly one
terminal nullary relation: it appears as a rule destination, never as a rule
source, and there is no explicit query or false-headed assertion. Zero or
multiple terminal nullary relations remain parse errors because choosing one
would be ambiguous.

### 2. Numeric equality weakening

The original SeedMiner derives ordered bounds from arithmetic equality. For an
equality `a = b`, PyHorn now keeps:

- `a = b`;
- `a >= b`;
- `b >= a`.

This is important when equality is true initially but only one directional
bound is inductive. It turns examples such as `dillig01.smt2` from `unknown`
into `Success`.

### 3. Complete query-pattern projection

Mining the query body one conjunct at a time loses relationships imposed by the
source relation application. For example:

```smt2
(and (inv y y) (not (< y 2452)))
```

requires the candidate:

```text
x != y or y < 2452
```

rather than the independently mined formulas `x = y` and `y < 2452`.

PyHorn now projects and negates the complete bad-state pattern, including:

- repeated relation arguments;
- constants in relation arguments;
- nontrivial relation arguments;
- equalities connecting canonical predicate positions.

This fixes `s_triv_01.smt2` and related corner cases.

### 4. Universal closure of query-local witnesses

A rule-local variable in a query is existentially chosen in the bad state.
Negating the bad state therefore universally closes that variable in the
candidate. PyHorn now mines candidates such as:

```text
forall j. 0 < j < i -> a[j] = b[j]
```

from array queries with a local index. This proves `array_copy_ind.smt2` and
other quantified array examples that were previously outside the candidate
language.

### 5. Candidate transfer across transparent phase changes

Multiple-predicate benchmarks often contain rules such as:

```text
P(x, y) -> Q(x, y)
```

or a pure permutation of arguments. A candidate observed in one phase is a
useful syntactic candidate in the other phase. SeedMiner now propagates
candidates in both directions across body-`true`, bijective variable-renaming
rules. MultiHoudini still proves or removes each copied candidate, so transfer
does not weaken soundness.

### 6. Quantified countermodel fallback

For a satisfiable combined violation, `model.eval(ForAll(...))` may remain
non-Boolean even though at least one candidate is refuted. Earlier code could
raise an internal error because no candidate was selected for removal.

PyHorn now:

1. attempts batch removal using the combined countermodel;
2. if evaluation is inconclusive, checks each active destination candidate
   individually under the same source assumptions;
3. removes every individually refuted candidate;
4. reports conservative `unknown` on a Z3 `unknown` or an unattributable SAT
   result instead of crashing.

### 7. Independent final certification

Persistent incremental solvers are used only for Houdini filtering. Before
returning `Success`, every original CHC is reconstructed and checked in a fresh
solver under the final candidate conjunctions. This prevents stale assumptions,
unbalanced scopes, or filtering-context defects from causing a false success.

## Seed-Houdini results

| Suite | Success | Unknown | Errors |
|---|---:|---:|---:|
| `bench_horn` | **115** | 237 | 0 |
| `bench_horn_cex` | **0** | 79 | 0 |
| `bench_horn_multiple` | **29** | 147 | 0 |

Detailed aggregate statistics:

| Suite | Initial candidates | Removed | Retained | Solver checks | Fresh certification checks |
|---|---:|---:|---:|---:|---:|
| `bench_horn` | 3,691 | 2,513 | 1,178 | 3,840 | 1,015 |
| `bench_horn_cex` | 949 | 667 | 282 | 1,157 | 275 |
| `bench_horn_multiple` | 2,943 | 2,179 | 764 | 3,696 | 827 |

The most important soundness result is that **none of the 79 known
counterexample benchmarks was reported as `Success`**.

`unknown` is intentionally conservative. It includes insufficient candidates,
reachable errors, and Z3 timeout/incomplete-quantifier results.

## Bounded exploration results

The bounded explorer was also exercised independently of Seed-Houdini.

| Suite/configuration | Counterexample | No counterexample within bound | Z3 unknown |
|---|---:|---:|---:|
| `bench_horn`, pool mode, bound 10 | 0 | 339 | 13 |
| `bench_horn_cex`, pool mode, bound 30 | 65 | 10 | 4 |
| `bench_horn_multiple`, pool mode, bound 10 | 0 | 175 | 1 |

The remaining ten counterexample-suite files require a deeper bound than 30 or
have no counterexample in the explored encoding. Four runs stopped on a Z3
`unknown`, principally quantified formulas. Bounded exploration never reported
a counterexample in either safe-oriented suite at bound 10.

## Checked-in corner-case examples

`examples/freqhorn_corner_cases/` contains six source benchmarks covering:

- unique implicit terminal query inference;
- equality-derived numeric bounds;
- repeated query arguments;
- quantified array candidates;
- partial quantified model evaluation;
- an unsafe quantified array case.

These examples are exercised by `tests/test_freqhorn_corner_cases.py` and do
not require the external FreqHorn repository.

## Remaining candidate-language gaps

The audit also exposed cases that cannot be solved by syntactic SeedMiner plus
conjunctive Houdini alone.

### Affine relations

`exact_iters_*.smt2` needs relations such as `i + 2*j = 20`. The relevant
linear combination is not an explicit Boolean subtree and requires grammar-
based or algebraic candidate generation.

### Modular and path-sensitive invariants

`s_split_09.smt2` and `s_split_10.smt2` require congruence information combined
with path/threshold disjunctions. Query avoidance alone is not inductive over
all states satisfying the candidate.

### ITE-derived finite ranges

`n_c11.smt2` requires a tighter reachable range induced by an `ite`, not merely
the query property. This needs ITE unfolding plus reachability-oriented range
synthesis.

### Array normalization and range synthesis

The original FreqHorn SeedMiner performs dedicated `select`/`store` rewriting,
array-access collection, iterator-range extraction, and array candidate
normalization. PyHorn now handles exact query-derived quantified candidates but
does not yet reproduce the full array candidate factory.

### Nonlinear and auxiliary expressions

The original implementation rewrites nonlinear subterms to auxiliary variables
and records constants and coefficients for later grammar generation. PyHorn's
current SeedMiner records syntactic candidates only; it does not yet synthesize
new polynomial or auxiliary-variable candidates.

### Solver incompleteness for quantifiers

Some quantified candidates cause Z3 to return `unknown` with reasons such as
`(incomplete quantifiers)` or `canceled`. These are reported conservatively.

## Reproducing the audit

Parse and type-check a suite:

```bash
PYTHONPATH=src python3 tools/check_chc_corpus.py /path/to/bench_horn
```

Run SeedMiner and MultiHoudini:

```bash
PYTHONPATH=src python3 tools/check_seed_houdini_corpus.py \
  /path/to/bench_horn \
  --timeout 1000 \
  --random-seed 1 \
  --json
```

Run the bundled corner-case regressions:

```bash
python3 -m pytest -q tests/test_freqhorn_corner_cases.py
```

## Acceptance properties retained by this audit

1. Every original benchmark parses or receives a specific ambiguity error.
2. Every candidate is predicate-local after projection/quantification.
3. Houdini candidate sets only shrink.
4. A candidate is removed only after a satisfiable refutation check.
5. Z3 `unknown` is never treated as validity.
6. `Success` requires fresh validation of every original CHC.
7. Known counterexample benchmarks never produce `Success`.
