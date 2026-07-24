# Seed-Houdini examples

- `counter_safe.smt2`: query negation supplies `x <= 10`; MultiHoudini
  removes weaker or non-inductive seeds and proves all clauses.
- `counter_unsafe.smt2`: the error is reachable; all useful seeds are removed
  and final query validation reports `unknown`.
- `multiple_predicates.smt2`: candidates are maintained separately for `p` and
  `q` and propagated through a cross-predicate rule.

Run, for example:

```bash
pyhorn-expl --seed-houdini --print-invariants counter_safe.smt2
```
