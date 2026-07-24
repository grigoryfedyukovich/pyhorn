# Incremental solver specification for PyHorn MultiHoudini

**Version:** 0.0.11  
**Status:** normative implementation specification

## 1. Purpose

This document specifies the logical checks, solver lifecycle, weakening
algorithm, quantified-candidate fallback, and independent certification used by
`MultiHoudini`.

## 2. Candidate interpretation

For each predicate `P`, the active finite candidate set `A_P` represents:

```text
I_P(v) = and(c(v) for c in A_P)
```

An empty set represents `true`. Candidate sets only shrink during a run.

## 3. CHC obligations

For a fact `B(x) -> P(t)`, validity is checked by the unsatisfiability of:

```text
B(x) and not I_P(t)
```

For a transition `P(s) and B(x) -> Q(t)`:

```text
I_P(s) and B(x) and not I_Q(t)
```

For a query `P(s) and B(x) -> false`:

```text
I_P(s) and B(x)
```

`Success` requires every corresponding formula to be UNSAT.

## 4. Persistent filtering contexts

A persistent context is created only for a non-query rule whose destination
predicate initially has at least one candidate. Query rules and rules with
`true` destination invariants need no filtering context.

Each context permanently asserts:

1. the normalized rule body;
2. for every initial source candidate `c`, a guarded implication:

```text
guard_c -> c(source_arguments)
```

Removed source candidates remain encoded but their guards are omitted from
subsequent checks.

Destination candidate instances are constructed once and retained as Z3 ASTs,
but are not permanently asserted.

## 5. Incremental filtering check

For the current active source set, the solver receives exactly the corresponding
guards as check assumptions.

For active destination candidates `d1 ... dn`, it temporarily asserts:

```text
not d1(destination_arguments) or ... or not dn(destination_arguments)
```

The check is performed inside one scope:

```python
solver.push()
try:
    solver.add(violation_disjunction)
    result = solver.check(*active_source_guards)
    model = solver.model() if result == z3.sat else None
    reason = solver.reason_unknown() if result == z3.unknown else None
finally:
    solver.pop()
```

The model and `reason_unknown()` must be captured before `pop()`.

Assumptions are used for source candidates because the active set shrinks in a
non-stack order. `push()`/`pop()` is used for the destination disjunction
because assumptions alone would conjoin negated candidates instead of forming
the required disjunction.

## 6. Countermodel weakening

On SAT, the combined model is evaluated against every active destination
candidate. Every candidate evaluated `false` is removed in one batch.

Quantified formulas may not evaluate to a concrete Boolean. If no candidate is
identified from the model, MultiHoudini performs individual checks:

```text
rule body
and active source invariant
and not candidate_i(destination_arguments)
```

Every individually SAT candidate is removed. An individual `unknown` is
recorded. If no refuted candidate can be attributed despite the combined SAT
result, the analysis returns conservative `unknown` rather than throwing or
continuing unsoundly.

## 7. Fixed point and termination

Rules are processed sequentially and removals take effect immediately. A SAT
filtering result removes at least one candidate or terminates with `unknown`.
Because no candidates are added, at most the initial total number of candidates
can be removed. The final no-change pass establishes a Houdini fixed point for
all filtering rules.

## 8. Independent certification

Filtering contexts are not trusted to certify the final answer. After the fixed
point, MultiHoudini creates a fresh solver for every original CHC and directly
asserts:

- the rule body;
- all final source candidates instantiated at source arguments;
- for non-query rules, the disjunction of negated final destination candidates.

A non-query rule with an empty destination set is valid trivially because its
destination invariant is `true` and requires no solver call.

The result is `Success` only if every performed fresh certification check is
UNSAT. SAT or `unknown` produces overall `unknown` with the responsible rule,
reason, and model when available.

This fresh pass isolates the final answer from leaked scopes, stale assumptions,
or persistent-context construction defects.

## 9. Statistics

`HoudiniStatistics` records:

- outer iterations;
- persistent filtering contexts;
- total solver checks, including individual quantified probes and certification;
- initial, removed, and remaining candidates;
- combined countermodels;
- unknown checks;
- fresh certification checks.

CLI JSON and debug output must include `certification_checks`.

## 10. Soundness requirements

1. Every temporary scope is restored in `finally`.
2. Active source assumptions exactly match active candidate keys.
3. A candidate is removed only after a SAT refutation.
4. `unknown` is never interpreted as UNSAT.
5. Candidate instantiation is simultaneous and sort/arity preserving.
6. Query-local variables in mined candidates are bound, not left foreign/free.
7. `Success` requires fresh validation of every original CHC.
8. Known counterexample benchmarks must never produce `Success`.

## 11. Multi-solver effectiveness

The natural reuse unit for Houdini is one rule, not a trace prefix. Repeated
checks for a rule share the body, source candidate instances, and destination
candidate instances while only assumptions and the active violation change.
This makes a persistent per-rule solver useful, especially for large formulas
or multiple weakening iterations.

The bounded explorer's longest-common-prefix pool should not be reused here:
unrelated CHCs do not form formula prefixes, and mutating a solver between rules
would destroy the stable rule-specific state.

Memory is controlled partly by lazy context creation. A future hard context cap
would need a value-aware rebuild policy; plain LRU can thrash because every
active rule may be revisited each Houdini iteration.

## 12. Required tests

- fact, transition, cross-predicate, and query obligations;
- candidate removal under assumptions;
- balanced scopes on SAT, UNSAT, unknown, and exceptions;
- batch removal of multiple candidates;
- individual quantified-candidate fallback;
- unattributable SAT becomes `unknown`;
- lazy context count;
- fresh certification count and failure reporting;
- equivalent results under repeated `SeedMiner.mine()`;
- no success on unsafe quantified examples.
