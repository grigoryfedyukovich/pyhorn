# Exact trace-candidate template specification

**Applies to:** PyHorn 0.0.17  
**Implementation:** `src/pyhorn_bnd/trace_miner.py`  
**Stable API:** `TraceTemplateId`, `trace_template_specifications()`  
**CLI:** `pyhorn-expl --list-trace-templates [--json]`

This document is exhaustive. `TraceCandidateMiner` emits no candidate family
outside the registry below. Each emitted `TraceCandidateObservation` contains:

- `template_id`: a stable `TraceTemplateId` value;
- `kind`: an instance label containing argument indices or feature names;
- `candidate`: the concrete Z3 Boolean formula;
- `sample_count`: the number of retained samples for that predicate.

The `kind` string is diagnostic and is not a stable API. `template_id` is the
stable identifier.

## Sampling and feature construction

For each non-query predicate `P`, the miner keeps at most
`max_samples_per_relation` distinct concrete destination states. States are
deduplicated by the SMT representation of their model values.

A template is evaluated only when every required argument has a supported
concrete model value in every retained sample:

- Boolean templates require Z3 Boolean values;
- numeric templates require exact integer or rational values;
- string templates require concrete Z3 string values;
- arrays, bit-vectors, algebraic irrational values, uninterpreted values, and
  partially interpreted terms do not currently create trace templates.

The base numeric feature vector, in predicate-argument order, contains:

1. each `Int` or `Real` argument directly;
2. `str.len(s)` for each concrete `String` argument.

For every unordered pair of base numeric features `(f_i, f_j)` with `i < j`,
the miner also constructs the difference feature `f_i - f_j`. Difference
features participate in constant, bound, and congruence templates. They do not
participate as separate columns in affine-nullspace inference.

All emitted formulas are simplified with `z3.simplify`, deduplicated by
`sexpr()`, and discarded if they simplify to `true`, `false`, or a non-Boolean
term. The per-predicate candidate limit is applied after this normalization in
generation order.

## Complete template registry

### `boolean.always-true`

Formula:

```smt2
b
```

Applies to one Boolean predicate argument `b`. Emitted exactly when every
retained sample evaluates `b` to `true`.

### `boolean.always-false`

Formula:

```smt2
(not b)
```

Applies to one Boolean predicate argument `b`. Emitted exactly when every
retained sample evaluates `b` to `false`.

### `numeric.constant`

Formula:

```smt2
(= f c)
```

`f` may be:

- an integer or real predicate argument;
- the length of a string predicate argument;
- the difference of two base numeric features.

Emitted when every exact sampled value of `f` is the same rational `c`.
Integer-valued features require an integral `c`.

A constant integral feature may additionally emit congruence candidates for
multiple moduli.

### `numeric.lower-bound`

Formula:

```smt2
(>= f c_min)
```

For the same feature classes as `numeric.constant`. Emitted when at least two
distinct values were observed, with `c_min` equal to the exact minimum sampled
value.

### `numeric.upper-bound`

Formula:

```smt2
(<= f c_max)
```

For the same feature classes as `numeric.constant`. Emitted when at least two
distinct values were observed, with `c_max` equal to the exact maximum sampled
value.

### `integer.congruence`

Formula:

```smt2
(= (mod f m) r)
```

Applies only to integral features:

- integer predicate arguments;
- string lengths;
- differences of two integral base features.

For every integer modulus

```text
2 <= m <= max_congruence_modulus
```

the miner emits a candidate when all sampled values of `f` have the same
residue `r` modulo `m`. It emits every qualifying modulus, not only the
smallest or strongest one.

### `numeric.affine-equality`

Formula schema:

```smt2
(= (+ (* a_1 f_1) ... (* a_n f_n) a_0) 0)
```

The feature columns are only the base numeric features: numeric arguments and
string lengths. Conditions:

- the number of base features is between 2 and 8 inclusive;
- at least two samples exist;
- rows of the exact rational matrix `[f_1 ... f_n 1]` are constructed from all
  retained samples;
- one candidate is generated for each basis vector returned by the miner's
  rational Gaussian-elimination nullspace routine;
- each vector is scaled to primitive integer coefficients by clearing
  denominators and dividing by their greatest common divisor;
- the sign is normalized so the first nonzero coefficient is positive;
- the candidate is discarded if any coefficient exceeds
  `max_affine_coefficient` in absolute value.

The miner emits a basis of observed affine equalities, not every linear
combination of that basis. It does not infer affine inequalities.

### `string.constant`

Formula:

```smt2
(= s "w")
```

Emitted when every retained sample gives the same concrete string `w` for
argument `s`.

### `string.common-prefix`

Formula:

```smt2
(str.prefixof "p" s)
```

`p` is the longest common prefix of all sampled strings for `s`. Emitted only
when `p` is nonempty.

### `string.common-suffix`

Formula:

```smt2
(str.suffixof "q" s)
```

`q` is the longest common suffix of all sampled strings for `s`. Emitted only
when `q` is nonempty.

### `string.observed-alphabet-closure`

Formula schema:

```smt2
(str.in_re
  s
  (re.*
    (re.union
      (str.to_re "c_1")
      ...
      (str.to_re "c_k"))))
```

The alphabet is the sorted set of distinct Unicode characters appearing in all
sampled values of `s`. Emitted when the alphabet size is between 1 and 16
inclusive. Empty strings contribute no characters. This template permits any
string over the observed alphabet; it does not preserve order or character
counts.

### `string.equality`

Formula:

```smt2
(= s_i s_j)
```

For each unordered pair of distinct string arguments, emitted when every
sampled pair has identical concrete values.

### `string.prefix-relation`

Formula:

```smt2
(str.prefixof s_i s_j)
```

For both orientations of every pair of distinct string arguments, emitted when
all sampled values of `s_j` start with the corresponding sampled value of
`s_i`.

### `string.suffix-relation`

Formula:

```smt2
(str.suffixof s_i s_j)
```

For both orientations of every pair of distinct string arguments, emitted when
all sampled values of `s_j` end with the corresponding sampled value of
`s_i`.

### `string.concatenation`

Formula:

```smt2
(= s_t (str.++ s_l s_r))
```

Enabled only when the predicate has at most five concrete string arguments.
The miner examines every ordered permutation of three distinct argument
positions `(t, l, r)` and emits the formula when every sample satisfies:

```text
value(s_t) = value(s_l) ++ value(s_r)
```

Repeated operands such as `s_t = s_l ++ s_l`, constants, and concatenations of
more than two operands are not generated.

## Parameters that change the template space

| Constructor option | Effect |
|---|---|
| `max_congruence_modulus` | Largest tested modulus; default 8 |
| `max_affine_coefficient` | Rejects normalized affine vectors with a larger absolute coefficient; default 64 |
| `max_candidates_per_relation` | Truncates unique candidates in generation order; default 256 |
| `max_samples_per_relation` | Limits the sample set used by all templates; default 64 |

Sampling depth, prefix limits, model count, timeout, and random seed can also
change the observed sample set and therefore the generated formulas.

## Deliberately unsupported templates

The trace miner currently does not generate:

- strict numeric inequalities unless simplification creates one indirectly;
- octagonal forms other than bounds on the fixed difference `f_i - f_j`;
- general inequalities `a_1 f_1 + ... + a_n f_n <= c`;
- nonlinear polynomial relations;
- products or ratios of features;
- disjunctions, implications, conditional invariants, or case splits;
- quantified formulas;
- array-content or array-index invariants;
- bit-vector masks, extracts, signed ranges, or modular arithmetic on bit-vectors;
- arbitrary regexes or inferred automata;
- substring, containment, replacement, or index relations;
- string length inequalities involving constants not observed as extrema;
- concatenation with constants or repeated operands;
- templates over uninterpreted sorts.

These omissions are completeness limitations only. Every generated formula is
still filtered by MultiHoudini and independently certified before `Success`.

## Programmatic access

```python
from pyhorn_bnd import trace_template_specifications

for item in trace_template_specifications():
    print(item.template_id.value)
    print(item.formula_schema)
    print(item.emission_condition)
```

Machine-readable CLI output:

```bash
pyhorn-expl --list-trace-templates --json
```

The checked-in JSON snapshot is
[`trace_candidate_templates.json`](trace_candidate_templates.json).
