# Real arithmetic support

**Version:** 0.0.12  
**Status:** implementation and regression-test contract

## 1. Semantics

PyHorn represents SMT-LIB `Real` terms directly as native Z3 ASTs. It does not
translate real values through Python `float` and does not approximate them.
Decimal literals and divisions of rational numerals are exact. For example:

```smt2
0.25
(/ 1.0 4.0)
```

both denote the exact rational value `1/4` after Z3 simplification.

This support is distinct from SMT-LIB floating-point sorts. `Real` denotes the
mathematical real numbers; IEEE-754 `FloatingPoint` is not advertised as part
of the invariant-mining contract.

## 2. Accepted inputs

Both supported CHC dialects may use real sorts.

### Fixedpoint syntax

```smt2
(declare-rel inv (Real))
(declare-var x Real)
(rule (inv 0.0))
(rule (=> (and (inv x) (< x 1.0)) (inv (+ x (/ 1.0 4.0)))))
```

### Pure SMT-LIB assertions

```smt2
(set-logic HORN)
(declare-fun inv (Real) Bool)
(assert (inv (/ 1.0 2.0)))
(assert
  (forall ((x Real))
    (=> (inv x) (inv (+ x (/ 1.0 2.0))))))
```

Relations may mix `Int` and `Real` arguments. Z3's inserted or explicit
`to_real` coercions remain in the normalized AST and in mined candidates.

## 3. Parsing and normalization

The parser preserves the declared sorts of:

- relation arguments;
- outer rule variables;
- nested quantified variables;
- array index and element sorts;
- relation-argument expressions; and
- interpreted assertion heads.

`HornProgram.arithmetic_sorts` records whether the normalized program uses
integer arithmetic, real arithmetic, or both:

```python
program = parse_chc_file("input.smt2")
program.arithmetic_sorts.uses_integer
program.arithmetic_sorts.uses_real
program.arithmetic_sorts.is_mixed
```

The profile is informational; it does not rewrite or weaken the input.

## 4. Bounded exploration

SSA state variables and rule-local variables are created using the original Z3
sorts. A real predicate argument therefore receives real-valued positional SSA
variables. No integer proxy or finite discretization is introduced.

Both bounded solver modes operate over the same exact formulas:

```text
--solver-mode pool
--solver-mode fresh
```

A reported real counterexample is a satisfiable exact Z3 model for the finite
unrolling. Nonlinear real constraints are handed to Z3 unchanged.

## 5. SMT dumps

`--dump-smt` declares compact `__bnd_var_N` and `__loc_var_N` symbols with their
actual sorts. A real-only trace contains `Real` declarations rather than `Int`
declarations and can be replayed by Z3:

```smt2
(declare-fun __bnd_var_0 () Real)
(assert ...)
(check-sat)
```

## 6. SeedMiner

Canonical variables use each predicate argument's declared sort. SeedMiner can
therefore mine and project candidates such as:

```text
x <= 1
x = 1/4
r <= ToReal(i)
select(a, i) = 1/2 * ToReal(i)
forall y:Real. ...
```

Numeric equality weakening applies to both integer and real ordered arithmetic:
from `a = b`, SeedMiner retains the equality and derives `a >= b` and `b >= a`.
Disequality variants use the total order of `Int` and `Real`.

SeedMiner remains syntactic. Real support does not imply complete affine,
polynomial, or nonlinear invariant synthesis.

## 7. MultiHoudini

MultiHoudini does not distinguish integer candidates from real candidates. It
instantiates native Z3 formulas at typed relation arguments, uses assumption
literals for active source candidates, and checks destination violations in Z3.

Fresh final certification reconstructs every CHC with the retained exact real
formulas. `Success` is returned only when all certification obligations are
UNSAT. A timeout or unsupported nonlinear/quantified reasoning path yields the
conservative result `unknown`.

## 8. Supported operator families

The tested contract includes:

- `+`, unary and binary `-`;
- `*`, including nonlinear multiplication passed through to Z3;
- `/` over real terms;
- `=`, `distinct`, `<`, `<=`, `>`, and `>=`;
- `ite` with real branches;
- explicit and parser-inserted `to_real`;
- arrays with real index or element sorts;
- `select` and `store` involving real values; and
- universal quantification involving real terms.

`div` and `mod` are integer operators. PyHorn preserves them for integer terms
but does not reinterpret them as real division or remainder.

## 9. Regression examples

The following checked-in examples form the minimum real-arithmetic regression
set:

| Example | Coverage |
|---|---|
| `fixedpoint_safe.smt2` | linear real Houdini proof and exact quarters |
| `fixedpoint_unsafe.smt2` | bounded real counterexample in pool/fresh modes |
| `assert_unsafe.smt2` | pure quantified SMT-LIB HORN syntax over `Real` |
| `mixed_int_real_safe.smt2` | mixed state and `to_real` candidate |
| `array_real_safe.smt2` | real-valued arrays and quantified invariant |
| `integer_state_real_division_safe.smt2` | implicit `to_real` from `/` on integer state |
| `nonlinear_unsafe.smt2` | nonlinear real finite unrolling |
| `counter_safe.smt2` | `--cands` / `--validate-candidates` "confirmed real" path |
| `helper_lemma_safe.smt2` | `--cands` / `--validate-candidates` "potentially promising" path |

`tests/test_real_arithmetic.py` additionally checks sort preservation in SSA,
SMT dump replay, exact rational simplification, and the arithmetic-sort profile.

## 10. Candidate validation and external candidates

`--cands` (external candidate import), `--dump-cands`, `--validate-candidates`,
and `--dump-promising-candidates` are sort-generic by construction (see
`candidate_validation.py` and `cands.py`: neither module ever branches on
`IntSort`, and both build on the same SSA/canonical-variable machinery listed
in sections 4 and 6). `counter_safe.smt2` and `helper_lemma_safe.smt2`,
together with their paired files in `examples/cands/`, exercise both
`--validate-candidates` outcomes over `Real`:

- **Confirmed real**: `counter_safe.smt2` pairs a correct invariant
  (`x <= 10.0`) with a candidate that is true only at the initial fact
  (`x = 0.0`). MultiHoudini drops the latter after one transition step, and
  `--validate-candidates` confirms it reachable at depth 2.
- **Potentially promising**: `helper_lemma_safe.smt2` supplies, alone, a
  candidate (`y >= 1.0`) that is globally true but not locally inductive
  without its correlating fact. MultiHoudini's local induction check treats
  the uncorrelated variable as unconstrained and finds a
  counterexample-to-induction that no real execution can reach;
  `--validate-candidates` correctly reports this as promising rather than
  confirmed. `--dump-promising-candidates` on this file emits a
  `(declare-fun inv (Real Real) Bool)` verification obligation with native
  `Real` sorts, not an `Int` approximation.

See `tests/test_candidate_validation_theories.py` and
`tests/test_cands_theories.py` for the corresponding regression tests, and
`docs/candidate_validation_theory_coverage.md` for the cross-theory summary.

## 11. Limitations

- Nonlinear real arithmetic may be expensive or return `unknown` under the
  configured per-check timeout.
- SeedMiner does not synthesize arbitrary linear combinations such as
  `2*x - 3*y <= 7` unless a related expression appears in the CHCs.
- Mathematical `Real` support does not add IEEE floating-point reasoning.
- Transcendental functions are not part of the tested CHC/invariant contract.
