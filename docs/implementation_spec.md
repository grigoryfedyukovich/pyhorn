# PyHorn implementation specification

**Version:** 0.0.18  
**Status:** implementation contract and regression-test specification

## 1. Supported input

PyHorn accepts linear constrained Horn clauses in either form:

- Z3 fixedpoint commands: `declare-rel`, `declare-var`, `rule`, and `query`;
- pure HORN assertions: Bool-valued `declare-fun`, quantified `assert`, and
  `check-sat`.

Z3 parses expressions. PyHorn performs a lightweight command scan to discover
relation names. Inputs using the String/sequence sort family are translated
from fixedpoint commands to equivalent quantified SMT-LIB assertions and
parsed with `z3.parse_smt2_string()`, because Z3's fixedpoint command parser
does not accept those sorts. Other inputs continue to use
`Fixedpoint.parse_string()`.
A normalized clause may contain at most one positive relation application in
its body. Nonlinear CHC bodies are rejected explicitly.

If a legacy file omits an explicit query, PyHorn infers one only when there is
exactly one terminal nullary relation. Ambiguous files with multiple terminal
nullary relations are rejected.

## 2. Normalized program representation

`HornProgram` stores normalized `HornRule` objects, relation/query sets,
outgoing graph indices, source symbol names, source path, slicing status, an
`ArithmeticSortProfile`, and a `StringSortProfile`. Every relation
application is checked for arity and sort consistency. `Int`, `Real`, mixed
`Int`/`Real`, `String`, regular-expression, nested quantified, and array
index/element sorts are preserved as native Z3 sorts. The string profile
reports `uses_string`, `uses_regular_expressions`, and
`uses_length_constraints`; the last flag is set when a normalized expression
contains `str.len`.

SMT-LIB `Real` values are exact mathematical reals. Decimal literals are never
converted through Python floating-point values. The detailed contract is in
[`real_arithmetic.md`](real_arithmetic.md).

## 3. Bounded exploration

For each requested length, the explorer exhaustively enumerates connected
ENTRY-to-query traces. Enumeration uses an explicit stack and linked paths, so
extension is O(1). An UNSAT-prefix trie prunes extensions of infeasible traces.

### 3.1 SSA construction

A positional SSA step is deterministic for `(rule_id, step_index)`. Steps and
state versions are stored in bounded LRU caches. The default limit is 65,536
entries and is configurable with `--max-ssa-cache-steps`; `0` is unlimited.

### 3.2 Solver modes

- `pool`: at most 16 retained incremental solvers by default; selects a
  longest-common-prefix context, pops its divergent suffix, and pushes/checks
  the new suffix.
- `fresh`: one new solver per trace, monotonic `add()`/`check()`, no
  `push()`/`pop()`.

### 3.3 SMT dumps

`--dump-smt DIR` emits every checked trace using:

```text
<benchmark>_k<bound>[_t<trace>]_<sat|unsat|unknown>.smt2
```

Each file contains one conjunctive assertion and `check-sat`, with compact
`__bnd_var_N` and `__loc_var_N` names compatible with the C++ explorer style.

## 4. SeedMiner

SeedMiner creates canonical typed variables for every non-query predicate and
walks Boolean parse-tree nodes from facts, transitions, and queries.

Required behavior:

- `mine()` is idempotent;
- candidates contain only canonical variables of one predicate, plus variables
  bound by their own quantifiers;
- arithmetic equality keeps the equality and derives both one-sided bounds;
- the complete query bad-state pattern is projected, including repeated and
  nontrivial relation arguments;
- query-local free variables are universally closed after bad-state negation;
- candidates propagate across pure bijective predicate-renaming rules;
- free-variable and direct-argument operations use stable Z3 AST IDs.

The candidate language is syntactic. It does not yet synthesize arbitrary
affine, modular, polynomial, or array-range invariants.

## 4a. Candidate mutation (`--mut`)

Optional, applied after mining/`--cands` merging and before MultiHoudini
runs. Ported from and extends FreqHorn's
`RndLearnerV3.hpp::mutateHeuristicEq`.

Required behavior:

- operates per-relation; never combines candidates from two different
  predicates;
- equalities: for every unordered pair of numeric equalities already in a
  relation's pool, derives four candidates via `+`/`-` across the direct
  and swapped pairings (ported as-is from the original);
- inequalities (new, not in the original): normalizes `>=`/`>` to
  `<=`/`<` form first, then for every ordered pair where one's right-hand
  side is syntactically the other's left-hand side, derives the
  transitive chain, strict if either input was;
- runs exactly one pass: derived candidates are not themselves re-mutated;
- drops results that simplify to `True`/`False` or duplicate a candidate
  already present;
- requires `--seed-houdini` or `--cands`.

Not ported: the original's constant-multiple substitution pass.

## 5. MultiHoudini

Filtering contexts are created lazily for non-query rules whose destination has
at least one candidate. A context permanently stores:

- the rule body;
- guarded source candidate instances.

Each filtering check passes active source guards as assumptions and temporarily
asserts the disjunction of negated active destination candidates in a balanced
`push()`/`pop()` scope.

A SAT countermodel removes every destination candidate evaluated false. If
quantified model evaluation is inconclusive, candidates are checked one by one
under the same source assumptions. Z3 `unknown` and unattributable SAT results
produce conservative `unknown`, never an internal success or crash.

After filtering reaches a fixed point, every original CHC is certified using a
new solver. `Success` is returned only if all certification checks are UNSAT.

Detailed solver semantics are specified in
[`houdini_incremental_solver_spec.md`](houdini_incremental_solver_spec.md).

## 6. Trace-template candidate generation (`--trace-houdini`)

`TraceCandidateMiner` samples satisfiable bounded prefixes and instantiates a
closed registry of 15 template families. Every observation carries a stable
`TraceTemplateId`; instance-specific `kind` labels are diagnostic only. The
complete formula schemas, feature construction, orientation rules, parameter
limits, and emission conditions are specified in
[`trace_candidate_templates.md`](trace_candidate_templates.md) and exposed by
`trace_template_specifications()` / `--list-trace-templates --json`.

`run_trace_houdini()` is staged: ordinary SeedMiner + MultiHoudini runs
first, and trace sampling is invoked only when that baseline does not prove
the program, so it is monotonic with respect to plain `--seed-houdini`
successes. See [`trace_model_generalization.md`](trace_model_generalization.md)
for the full design and current evaluation. No trace-derived candidate has
proof authority: candidates are merged with syntactic seeds, filtered by
MultiHoudini, and certified with fresh solvers, exactly as in section 5.

`run_trace_houdini()` also accepts `mutate=True` (wired to `--mut`), applying
`mutate_candidates()` to the candidate set live at each of its own stages --
the seed-mined set for the baseline attempt, and the full seed-plus-trace
set for the second stage -- so `--mut` sees the complete combined pool
available at that point, whichever sources contributed to it.

`mutate_candidates()`'s pairing cost is quadratic in the number of
equalities/inequalities per relation, and trace-sampled pools routinely
carry far more of those than the syntactically-mined pools it was
originally sized for -- unbounded, this made `--trace-houdini --mut` take
on the order of tens of minutes on array-heavy benchmarks with large
combined candidate pools (see `test_trace_houdini_mut_bounds_large_pools`
in `tests/test_trace_houdini.py` for a concrete case, reduced from 30+
minutes to under 30 seconds). `run_trace_houdini()` therefore passes
`max_terms_per_relation=DEFAULT_MAX_MUTATION_TERMS_PER_RELATION` (32) to
every `mutate_candidates()` call it makes, wired to `--trace-mutation-limit`
(`0` disables the cap). `mutate_candidates()`'s own default stays unbounded,
since plain `--seed-houdini`/`--cands` pools are not normally large enough
to need the cap.

`mutate_candidates()` also derives candidates through mechanisms beyond
numeric pairing, all subject to the same cost discipline:

- **Sort-agnostic equality substitution**: any equality `a = b` (not just
  arithmetic) rewrites every other candidate by substituting `b` for `a`
  and vice versa. Cost is linear in candidates × equalities, bounded from
  both sides -- `max_terms_per_relation` caps the equalities considered
  (this is what actually keeps the iteration itself bounded: an earlier
  version of this cap only applied to the numeric-pairing equality list,
  not the general one substitution draws from, which independently cost
  several seconds of pure loop overhead on a 400-equality synthetic pool
  even with the attempt cap below already engaged) and
  `max_equality_substitutions_per_relation` (default
  `DEFAULT_MAX_EQUALITY_SUBSTITUTIONS_PER_RELATION`, 256; wired to
  `--trace-mutation-substitution-limit`, `0` disables it) caps the total
  rewrite attempts, independent of how many equalities fed it.
- **Explicit String bridges** (linear, not paired): string equality → equal
  lengths; `prefixof`/`suffixof`/`contains` against a literal → a length
  lower bound; concat equality → length additivity, plus literal
  propagation through the concatenation (full equality when every operand
  is pinned, a `prefixof`/`suffixof` bound when only a leading/trailing
  run is).
- **Regex intersection**: two membership facts on the same subject combine
  into membership in their intersection, letting Z3's own regex simplifier
  do the theory work. Deliberately not extended to regex complement, given
  this codebase's own documented history of Z3 hanging on complement-heavy
  checks (`docs/candidate_validation_theory_coverage.md`).

A separate mode from `--cands` in this release (`--mut` and a redundant
`--seed-houdini` are both accepted directly, as above); not yet combinable
with `--cands` or `--validate-candidates` (see the migration notes
referenced from this repository's history for the planned unification).

## 7. Candidate-generator extension boundary

`CandidateGenerator` and `CandidateBatch` (see
[`candidate_generator_api.md`](candidate_generator_api.md)) define a neutral
proposal interface. `SeedMiner` and `TraceCandidateMiner` both implement it
today; a future machine-learning component could use the same canonical
predicate variables and produce finite Boolean Z3 formulas without changing
MultiHoudini or the certification boundary. `merge_candidate_batches()`
verifies variable compatibility, simplifies and deduplicates formulas, and
returns a normal `CandidateMap`. A generator's output is always untrusted
until Houdini filtering and fresh certification succeed.

User-supplied `--cands` files and `--mut` mutation predate this API and are
merged through `cands.merge_candidate_maps` instead; adapting them to the
same protocol is a natural follow-up, not yet done.

## 8. Error handling

Expected parse, normalization, and filesystem errors map to CLI exit code 3.
Unexpected internal exceptions are not hidden. Z3 `unknown` maps to analysis
status `unknown` and exit code 2.

## 9. Version and API

```python
import pyhorn_bnd
assert pyhorn_bnd.__version__ == "0.0.18"
```

Primary APIs:

```python
parse_chc_file(...)
BoundedExplorer(...).explore(...)
SeedMiner(...).mine()
MultiHoudini(...).run(...)
run_seed_houdini(...)
run_trace_houdini(...)
TraceCandidateMiner(...).mine()
trace_template_specifications()
merge_candidate_batches(...)
```

## 10. Required regressions

The test suite must cover:

- both input dialects;
- representative sorts and operators from `bench_horn`;
- all checked-in FreqHorn corner cases;
- optional parsing of the complete external corpus;
- deep non-recursive trace enumeration;
- SSA cache eviction and solver-pool reuse;
- C++-compatible SMT dump naming and equivalence;
- SeedMiner idempotence and predicate locality;
- omitted-query inference and ambiguity rejection;
- equality weakening and complete query-pattern candidates;
- quantified query candidate generation;
- quantified countermodel fallback;
- fresh final CHC certification;
- no `Success` for known unsafe regression examples;
- fixedpoint and pure-assert real arithmetic;
- exact rational literals and mixed `Int`/`Real` coercions;
- real-valued arrays, quantified real candidates, and nonlinear real traces;
- real-sort preservation in SSA and replayable SMT dumps;
- fixedpoint and pure-assert String CHCs;
- string equality, concatenation, length, search, replacement, conversion,
  and regex operators;
- mixed String/Int invariants and string-valued arrays;
- string-length equalities, inequalities, regex/length combinations, substring
  windows, and multi-predicate ghost-length relations;
- String-sort preservation in SSA and replayable SMT dumps;
- stable trace-template registry and JSON snapshot;
- stable template IDs on generated observations;
- bidirectional string prefix/suffix relation generation;
- neutral candidate-generator batch compatibility and merging;
- sort-agnostic equality substitution across Int/String/Array/Bool;
- explicit String↔Int bridges (equal-length, prefix/suffix/contains length
  bounds, concat length additivity, full and partial literal propagation);
- regex-membership intersection on a shared subject;
- mutation cost caps (`max_terms_per_relation`,
  `max_equality_substitutions_per_relation`) actually bounding iteration,
  not merely the reported counts.

The full benchmark evidence and remaining limitations are documented in
[`freqhorn_benchmark_audit.md`](freqhorn_benchmark_audit.md).
