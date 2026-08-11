# Trace-generalized candidate examples

These examples exercise candidate generation from bounded reachable-state
models.  The generated candidates are hypotheses only; MultiHoudini validates
all retained formulas before reporting `Success`.

```bash
pyhorn-expl --trace-houdini --trace-depth 8 integer_affine_safe.smt2
```

`array_tiling_pr4.smt2` is a performance regression fixture for
`--trace-houdini --mut` on array-heavy programs with large combined
candidate pools -- see the comment at the top of that file and
`--trace-mutation-limit` in the main README.
