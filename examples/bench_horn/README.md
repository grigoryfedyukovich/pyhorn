# Representative `bench_horn` parser cases

These files are small, unchanged CHC bodies extracted from the external
`bench_horn` corpus.  Only leading coverage comments and descriptive filenames
were added.

| File | Parser coverage |
|---|---|
| `01_int_linear.smt2` | Integer state, constants in relation arguments, equality, negation |
| `02_bool_state.smt2` | Boolean state and a bare Boolean constraint |
| `03_mixed_bool_int_mod_ite.smt2` | Mixed `Int`/`Bool`, nested `ite`, `mod` |
| `04_array_store_select.smt2` | Array state, `store`, `select` |
| `05_const_array_and_ite.smt2` | Multiple arrays, constant array, `ite`, `store`, `select` |
| `06_integer_div_mod.smt2` | Integer `div` and `mod` |
| `07_nonlinear_multiplication.smt2` | Nonlinear multiplication |
| `08_define_fun_or_ite.smt2` | `define-fun`, `or`, `ite` |
| `09_distinct_and_ite.smt2` | `distinct`, unary negation, `ite` |
| `10_real_division_coercion.smt2` | `/` over integer terms and inserted Real coercions |
