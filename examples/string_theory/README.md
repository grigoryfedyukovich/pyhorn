# String theory examples

Small linear CHCs that exercise SMT-LIB `String` and regular-expression
operators through PyHorn's parser, SSA builder, bounded explorer, and
Seed-Houdini pipeline.

| File | Focus | Expected |
|---|---|---|
| `operators_safe.smt2` | `len`, `prefixof`, `suffixof`, `contains`, `at`, `substr`, `indexof`, `replace`, `to_int`, `from_int` | safe |
| `regex_safe.smt2` | `str.in_re`, `re.*`, `str.to_re` | safe |
| `regex_union_range_safe.smt2` | `re.union`, `re.range`, `re.*` | safe |
| `mixed_string_int_safe.smt2` | length-tracked `String`/`Int` state | safe |
| `str_to_int_roundtrip_safe.smt2` | `str.from_int` / `str.to_int` round-trip | safe |
| `string_array_safe.smt2` | arrays with `String` elements | safe |
| `unicode_safe.smt2` | Unicode escapes and doubled quotes | safe |
| `concat_prefix_safe.smt2` | multi-step `str.++` with `prefixof` | safe |
| `empty_suffix_safe.smt2` | empty suffix invariant | safe |
| `fixedpoint_safe.smt2` | fixedpoint syntax, safe | safe |
| `fixedpoint_unsafe.smt2` | fixedpoint syntax, unsafe | unsafe |
| `fixedpoint_regex_safe.smt2` | fixedpoint + regex membership | safe |
| `assert_unsafe.smt2` | pure SMT-LIB assertions, unsafe | unsafe |
| `disequality_unsafe.smt2` | string disequality counterexample | unsafe |

See [`docs/string_theory.md`](../../docs/string_theory.md) for the support contract.
