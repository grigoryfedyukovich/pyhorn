# PyHorn implementation specification

**Version:** 0.0.11  
**Status:** implementation contract and regression-test specification

## 1. Supported input

PyHorn accepts linear constrained Horn clauses in either form:

- Z3 fixedpoint commands: `declare-rel`, `declare-var`, `rule`, and `query`;
- pure HORN assertions: Bool-valued `declare-fun`, quantified `assert`, and
  `check-sat`.

Z3 parses expressions. PyHorn performs one lightweight command scan to discover
relation names and passes the already-read source to `Fixedpoint.parse_string()`.
A normalized clause may contain at most one positive relation application in
its body. Nonlinear CHC bodies are rejected explicitly.

If a legacy file omits an explicit query, PyHorn infers one only when there is
exactly one terminal nullary relation. Ambiguous files with multiple terminal
nullary relations are rejected.

## 2. Normalized program representation

`HornProgram` stores normalized `HornRule` objects, relation/query sets,
outgoing graph indices, source symbol names, source path, and slicing status.
Every relation application is checked for arity and sort consistency.

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

## 6. Error handling

Expected parse, normalization, and filesystem errors map to CLI exit code 3.
Unexpected internal exceptions are not hidden. Z3 `unknown` maps to analysis
status `unknown` and exit code 2.

## 7. Version and API

```python
import pyhorn_bnd
assert pyhorn_bnd.__version__ == "0.0.11"
```

Primary APIs:

```python
parse_chc_file(...)
BoundedExplorer(...).explore(...)
SeedMiner(...).mine()
MultiHoudini(...).run(...)
run_seed_houdini(...)
```

## 8. Required regressions

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
- no `Success` for known unsafe regression examples.

The full benchmark evidence and remaining limitations are documented in
[`freqhorn_benchmark_audit.md`](freqhorn_benchmark_audit.md).
