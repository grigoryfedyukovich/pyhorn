# String and regular-expression support

**Version:** 0.0.14  
**Status:** implementation and regression-test contract

## 1. Semantics

PyHorn represents SMT-LIB `String` expressions directly as native Z3 sequence
ASTs. `String` denotes sequences of Unicode characters. PyHorn does not encode
strings as integers, byte arrays, or Python strings during reasoning.

String theory is generally incomplete when combined with arithmetic,
quantifiers, and regular expressions. A Z3 `unknown` result is therefore
reported conservatively and never establishes safety.

## 2. Accepted CHC syntax

Both input dialects support string-sorted predicates.

### Fixedpoint commands

```smt2
(set-logic HORN)
(declare-var s String)
(declare-rel inv (String))
(declare-rel fail ())
(rule (inv ""))
(rule (=> (and (inv s) (< (str.len s) 3))
          (inv (str.++ s "a"))))
(query fail)
```

### Pure SMT-LIB assertions

```smt2
(set-logic HORN)
(declare-fun inv (String) Bool)
(assert (inv ""))
(assert
  (forall ((s String))
    (=> (and (inv s) (< (str.len s) 3))
        (inv (str.++ s "a")))))
(check-sat)
```

## 3. Parser frontend

Z3's fixedpoint command parser does not accept the String/sequence sort family.
For inputs declaring `String`, `Seq`, `RegEx`, `RegLan`, `Char`, or `Unicode`,
PyHorn performs a syntax-preserving command translation:

- `declare-rel` becomes a Bool-valued `declare-fun`;
- `declare-var` declarations become universal binders on each rule/assertion;
- `rule` becomes `assert`; and
- `query` is recovered as a nullary query relation.

The translated text is parsed with `z3.parse_smt2_string()`. Non-string inputs
continue to use Z3's fixedpoint parser, preserving the established original-
benchmark behavior and performance.

## 4. Program profile

`HornProgram.string_sorts` reports whether the normalized program uses strings
and regular expressions:

```python
program.string_sorts.uses_string
program.string_sorts.uses_regular_expressions
```

The profile scans relation signatures, rule arguments, bodies, arrays, and
nested quantified sorts. It is informational and does not alter formulas.

## 5. Bounded exploration and SSA

SSA state variables and rule-local symbols use their original Z3 sorts. A
string predicate argument therefore receives a positional SSA variable declared
as `String`. The fresh and pooled solver modes check the same native formulas.

Compact `--dump-smt` output declares string and string-containing array symbols
with their exact sorts, for example:

```smt2
(declare-fun __bnd_var_0 () String)
(declare-fun __bnd_var_1 () (Array Int String))
```

The generated file is replayable by Z3.

## 6. SeedMiner and MultiHoudini

Canonical invariant variables inherit predicate argument sorts. SeedMiner can
therefore observe and project candidates such as:

```text
not contains(s, "bad")
length(s) = n
prefixof("abc", s)
in_re(s, re.*(to_re("a")))
select(a, i) = "ok"
```

String equality does not receive numeric ordering variants. Mixed formulas such
as `str.len(s) = n` may still produce numeric one-sided bounds because both
sides of that equality are integer expressions.

MultiHoudini treats string candidates like other Boolean Z3 formulas. It uses
assumption literals for source candidates, temporary destination-violation
scopes, countermodel-driven removal, and fresh final certification.

## 7. Tested operator families

The regression contract covers:

- `=`, `distinct`, and negation over strings;
- `str.++`;
- `str.len`;
- `str.at` and `str.substr`;
- `str.prefixof`, `str.suffixof`, and `str.contains`;
- `str.indexof`;
- `str.replace`;
- `str.to_int` and `str.from_int`;
- `str.in_re`, `str.to_re`, and `re.*`;
- arrays with `String` elements; and
- mixed `String`/`Int` relation signatures.

These operators are passed to Z3; PyHorn does not implement a separate string
solver.

## 8. Unicode literals

SMT-LIB Unicode escapes are preserved by the command scanner and general-parser
translation. For portable input, use standard escapes such as:

```smt2
"\u{3bb}"
```

A quote inside an SMT-LIB string is represented by doubling it:

```smt2
"a""b"
```

## 9. Regression examples

| Example | Coverage |
|---|---|
| `fixedpoint_safe.smt2` | fixedpoint syntax and a Houdini containment invariant |
| `fixedpoint_unsafe.smt2` | bounded string counterexample in both solver modes |
| `assert_unsafe.smt2` | pure SMT-LIB quantified assertions |
| `regex_safe.smt2` | regex membership candidate and certification |
| `mixed_string_int_safe.smt2` | exact string-length tracking |
| `string_array_safe.smt2` | arrays with String elements and dump replay |
| `operators_safe.smt2` | representative standard string operators |
| `concat_prefix_safe.smt2` | multi-step concat + prefixof |
| `regex_union_range_safe.smt2` | re.union / re.range / re.* |
| `str_to_int_roundtrip_safe.smt2` | from_int / to_int with Int state |
| `empty_suffix_safe.smt2` | empty suffix invariant |
| `fixedpoint_regex_safe.smt2` | fixedpoint syntax + regex |
| `disequality_unsafe.smt2` | string disequality counterexample |
| `unicode_safe.smt2` | Unicode escape and doubled-quote preservation |

## 10. Limitations

- The tested public contract is `String`; arbitrary non-string `Seq(T)` terms
  are not yet advertised as a complete SeedMiner contract.
- Regex-heavy or quantified string constraints may time out or return
  `unknown`.
- SeedMiner only retains syntactic candidates observed in CHCs; it does not
  synthesize general word equations or automata invariants.
- The alternative Z3 string solver backend is not currently exposed as a
  PyHorn command-line option; the installed Z3 default is used.
