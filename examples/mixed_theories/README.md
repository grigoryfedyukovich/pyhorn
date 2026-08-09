# Cross-theory combinations

`examples/real_arithmetic/` covers Int+Real combinations and
`examples/string_theory/` covers Int+String combinations, but neither
suite paired Real with String directly. This directory fills that gap.

| Example | Combination | Expected |
|---|---|---|
| `real_string_safe.smt2` | Real accumulator + String log, linked by `to_real (str.len ...)` | `Success` |
| `int_real_string_safe.smt2` | Int step counter + Real accumulator + String log, all three in one relation | `Success` |

Both are also used to test `--cands` / `--validate-candidates` over
theory combinations that were previously untested for those two features;
see `examples/cands/real_string_candidates.smt2` and
`examples/cands/int_real_string_candidates.smt2`, and
`tests/test_candidate_validation_theories.py`.

## A hard one

The two examples above are both easy: SeedMiner mines the exact linear
equality or coercion needed and MultiHoudini finds it immediately. That's
not representative of what genuinely hard theory-combination problems look
like, so this directory also has one this tool cannot solve:

| Example | Combination | Expected | Actual |
|---|---|---|---|
| `coffee_can_step_counter_safe.smt2` | Int step counter + the Gries coffee-can String rewriting system | `Success` (the property genuinely holds) | `unknown` |

It is `examples/string_invariant_literature/coffee_can_odd_white_safe.smt2`
with an orthogonal Int counter threaded through the signature, so String
combines with Int rather than standing alone. The counter itself is easy
and irrelevant to the property; the difficulty -- and the `unknown`
result -- is inherited unchanged from the parent example. See that file's
header comment and `tests/test_mixed_theories_hard.py` for why: the
invariant needed is that the number of `W` symbols stays odd, a
modular/parity fact no candidate mined syntactically from the rule or
query text can express, and this tool has no automata-learning backend to
derive it another way.
