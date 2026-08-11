# String invariants with length constraints

**PyHorn version:** 0.0.18  
**Benchmark directory:** `examples/string_length_literature/`

## Status update

Sections 5 ("Proposed `LengthSeedFactory`") and the "Immediate implementation
priorities" in section 8 below describe a design written before trace-guided
candidate generation (`--trace-houdini`, see
[`trace_model_generalization.md`](trace_model_generalization.md) and
[`trace_candidate_templates.md`](trace_candidate_templates.md)) existed.
`TraceCandidateMiner` now substantially realizes the linear-template (§5.3,
via the `numeric.affine-equality` template) and congruence-template (§5.4,
via the `integer.congruence` template) proposals below, by sampling
concrete bounded models rather than by the static transition-delta GCD
analysis originally sketched -- a different mechanism reaching a similar
result. In particular, `append_two_parity_safe.smt2` (§2, §7.7) is proved
`Success` under `--trace-houdini`, even though it remains `unknown` under
plain `--seed-houdini` as this document originally described. The interval
propagation (§5.5) and regex length summaries (§5.6) proposals are not yet
implemented by either pipeline.

## 1. Scope

This suite exercises linear CHCs that combine SMT-LIB strings with integer
arithmetic over `str.len`. The benchmarks are literature-derived verification
patterns, not verbatim copies of external benchmark files.

The SMT-LIB Unicode Strings theory defines `str.len : String -> Int`. Length is
therefore ordinary integer arithmetic and can occur in equalities,
inequalities, linear combinations, and mixed string/regex obligations.

Relevant literature and benchmark sources include:

- the SMT-LIB Unicode Strings theory;
- Kaluza and related symbolic-execution benchmark families, which combine
  concatenation, regex membership, equality, and length constraints;
- Z3str3 and other industrial string solvers supporting word equations, regular
  languages, and linear arithmetic over string length;
- length-aware regex solving, where upper and lower length bounds are used to
  simplify automata operations;
- stabilization-based solving for string equations with lengths; and
- HornStr, which represents string invariant-synthesis problems as CHCs.

References:

1. SMT-LIB Unicode Strings theory: <https://smt-lib.org/theories-UnicodeStrings.shtml>
2. P. A. Abdulla et al., *String Constraints for Verification*, CAV 2014.
3. M. Berzish, Y. Zheng, V. Ganesh, *Z3str3: A String Solver with
   Theory-aware Branching*, 2017.
4. M. Berzish et al., *An SMT Solver for Regular Expressions and Linear
   Arithmetic over String Length*, 2020.
5. T. Chen et al., *Solving String Constraints with Lengths by
   Stabilization*, PACMPL/OOPSLA 2023.
6. H. Jiang et al., *HornStr: Invariant Synthesis for Regular Model Checking
   as Constrained Horn Clauses*, CAV 2025.

## 2. Benchmark inventory

| Benchmark | Main operations | Expected | Current result | Required invariant |
|---|---|---:|---|---|
| `bounded_append_safe.smt2` | append, upper bound | safe | `Success` | `len(s) <= 8` |
| `bounded_append_unsafe.smt2` | append by two, faulty guard | unsafe | CEX depth 4 | — |
| `copy_length_conservation_safe.smt2` | `substr`, `at`, concat, ghost length | safe | `Success` | `len(rem)+len(out)=total` |
| `doubling_word_equation_safe.smt2` | word equation, affine length | safe | `Success` | `len(y)=2*len(x)` |
| `length_preserving_rewrite_safe.smt2` | local rewrite | safe | `Success` | `len(s)=n` |
| `password_policy_safe.smt2` | regex plus range `[8,12]` | safe | `Success` | regex membership and length bounds |
| `sliding_window_safe.smt2` | `substr`, index arithmetic | safe | `Success` | `len(window)=4` |
| `append_two_parity_safe.smt2` | append by two | safe | `unknown` under `--seed-houdini`; `Success` under `--trace-houdini` | `len(s) mod 2 = 0` |
| `length_counter_desync_unsafe.smt2` | string/counter mismatch | unsafe | CEX depth 3 | — |
| `multiphase_length_transfer_safe.smt2` | two predicates, append and drain | safe | `Success` | `len(s)=n` in both phases |

The expected results are regression contracts for plain `--seed-houdini`.
`unknown` is intentional for the parity benchmark under that mode because
the syntactic miner does not invent modular length templates; see the
status update above for how `--trace-houdini` resolves it.

## 3. What the current implementation already handles

### 3.1 Native parsing and typing

String terms and `str.len` remain native Z3 ASTs. No string-to-array or
string-to-integer encoding is introduced. The integer result of `str.len` may
be mixed with:

- integer constants;
- linear `+`, `-`, and multiplication by constants;
- strict and non-strict inequalities;
- ghost counters stored in predicate arguments;
- regular-expression membership; and
- substring indices and lengths.

`HornProgram.string_sorts.uses_length_constraints` reports whether a normalized
program contains a `str.len` application.

### 3.2 Bounded exploration

The SSA builder preserves both `String` state variables and integer length
expressions. Unsafe examples are solved by ordinary trace unrolling. The dumped
SMT-LIB contains the same `str.len` expressions and can be replayed directly in
Z3.

### 3.3 SeedMiner and MultiHoudini

The current pipeline succeeds when the needed invariant is already visible in
or is a simple arithmetic consequence of a CHC formula. Examples include:

```smt2
(<= (str.len s) 8)
(= (+ (str.len remaining) (str.len output)) total)
(= (str.len y) (* 2 (str.len x)))
(= (str.len window) 4)
```

SeedMiner projects these formulas onto canonical predicate variables.
MultiHoudini then removes non-inductive formulas and freshly certifies the
retained conjunction against every CHC.

## 4. Why length invariants are a distinct synthesis problem

Strings contribute arithmetic facts that need not appear syntactically in the
input. Important examples are:

```text
len(x ++ y) = len(x) + len(y)
len(substr(x, i, n)) is piecewise bounded by n and len(x)-i
x = y ++ z implies len(x) = len(y) + len(z)
append of a literal of length k changes length by k
length-preserving rewrite has delta 0
```

A solver may use these facts internally to decide one formula, but Houdini still
needs an explicit candidate to represent the invariant between CHC predicates.
The candidate miner therefore needs a dedicated length abstraction rather than
waiting for Z3 to invent the predicate interpretation.

## 5. Proposed `LengthSeedFactory`

A practical next component is a theory-specific candidate factory that runs
before MultiHoudini.

### 5.1 Length variables

For every string-valued predicate argument `s_i`, create a derived integer term:

```text
L_i = str.len(s_i)
```

Retain ordinary integer predicate arguments as additional dimensions. The
candidate space then becomes a finite template domain over:

```text
L_0, ..., L_m, n_0, ..., n_k
```

### 5.2 Direct length consequences

Walk rule bodies and relation arguments to generate consequences such as:

- `x = y` → `len(x) = len(y)`;
- `x = y ++ z` → `len(x) = len(y) + len(z)`;
- `x' = x ++ literal` → `len(x') = len(x) + |literal|`;
- `x' = substr(x, 1, len(x)-1)` under `len(x)>0` →
  `len(x') = len(x)-1`;
- replacement of equal-length literals → zero length delta;
- regex membership → minimum/maximum/congruence summaries when computable.

These consequences should be added as candidate templates, not assumed as
invariants. MultiHoudini remains responsible for proof and removal.

### 5.3 Linear templates

Generate bounded-coefficient affine forms:

```text
a_0*L_0 + ... + a_m*L_m + b_0*n_0 + ... + b_k*n_k = c
<= c
>= c
```

Start with coefficients from `{-2,-1,0,1,2}` and constants observed in the CHC.
Prioritize sparse forms with at most two or three nonzero terms.

This captures:

- length conservation;
- doubling relations;
- fixed windows;
- upper/lower buffer bounds; and
- string/counter synchronization.

### 5.4 Congruence templates

Transition deltas expose modular invariants. If all transitions for one
predicate change `len(s)` by multiples of `g`, and facts have residue `r`,
generate:

```smt2
(= (mod (str.len s) g) r)
```

For `append_two_parity_safe.smt2`, the fact has length `0` and every transition
adds `2`, yielding:

```smt2
(= (mod (str.len s) 2) 0)
```

The candidate must still pass MultiHoudini and fresh certification.

### 5.5 Interval propagation

Use simple abstract interpretation over rule-local length equations to infer:

- nonnegativity of all string lengths;
- upper bounds from guarded append loops;
- lower bounds from initial facts and monotone growth;
- fixed bounds for substring windows; and
- phase-specific intervals in multi-predicate systems.

Intervals can be proposed as Houdini candidates. This avoids embedding an
entire abstract interpreter into the trusted success path.

### 5.6 Regex length summaries

For regular expressions, compute or approximate:

- minimum accepted length;
- finite maximum length, when one exists;
- possible lengths modulo a small period;
- singleton/fixed-length languages.

Combine these summaries with the regex candidate. For a password policy, the
candidate is naturally a conjunction of language membership and `[8,12]`
length bounds.

## 6. Solver architecture

Recommended pipeline:

```text
parse CHCs
  -> SeedMiner syntactic candidates
  -> LengthSeedFactory arithmetic candidates
  -> optional DFA/regex candidates
  -> MultiHoudini filtering
  -> fresh CHC certification
```

The length factory is untrusted candidate generation. Soundness continues to
come from the final fresh Z3 certification.

For difficult combinations, a backend abstraction should permit checking with
Z3, cvc5, OSTRICH, or another SMT-LIB string solver. A backend returning
`unknown` must never be interpreted as proof.

## 7. Testing contract

Every length benchmark must satisfy:

1. parsing and normalization succeed;
2. `uses_string`, `uses_integer`, and `uses_length_constraints` are true;
3. every relation argument retains its declared sort;
4. the SSA dump contains `str.len` and replays in Z3;
5. supported safe cases return `Success` after fresh certification;
6. unsafe cases are found in both bounded solver modes at the documented
   minimal depth; and
7. the modular benchmark remains `unknown` under plain `--seed-houdini`
   until congruence generation is implemented there directly (it is already
   solved via sampled congruence generalization under `--trace-houdini`;
   see the status update above).

Run:

```bash
python3 -m pytest -q tests/test_string_length_literature.py
PYTHONPATH=src python3 tools/audit_string_length_benchmarks.py --json
```

## 8. Immediate implementation priorities

1. Add `LengthSeedFactory` with direct concatenation and substring equations.
2. Add sparse affine templates over string lengths and integer state.
3. Add transition-delta GCD analysis for modular candidates.
4. Add regex minimum/maximum/congruence summaries.
5. Benchmark candidate counts and Houdini time to prevent template explosion.
6. Keep independent fresh certification as the sole condition for `Success`.
