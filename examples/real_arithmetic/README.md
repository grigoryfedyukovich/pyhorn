# Real arithmetic examples

These examples exercise exact SMT-LIB `Real` support.

```bash
pyhorn-expl --seed-houdini fixedpoint_safe.smt2
pyhorn-expl --upto 8 fixedpoint_unsafe.smt2
pyhorn-expl --upto 8 assert_unsafe.smt2
pyhorn-expl --seed-houdini mixed_int_real_safe.smt2
pyhorn-expl --seed-houdini array_real_safe.smt2
pyhorn-expl --seed-houdini integer_state_real_division_safe.smt2
pyhorn-expl --upto 4 nonlinear_unsafe.smt2
```

Decimal and fractional values are exact Z3 rationals. The nonlinear example is
passed unchanged to Z3 and is intended to test bounded reasoning, not complete
nonlinear invariant synthesis.
