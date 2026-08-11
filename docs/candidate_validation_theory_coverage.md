# Candidate-validation theory coverage

**Status:** closes a gap identified in review; see below.

## The gap

A review of this codebase found that Linear Integer Arithmetic (LIA),
Linear Real Arithmetic (LRA), and String/regex were each genuinely
supported by the invariant checker, with real example files and a real
regression contract (`docs/real_arithmetic.md`, `docs/string_theory.md`),
including bounded exploration and SeedMiner/MultiHoudini (`--seed-houdini`)
across theory combinations (Int+Real, Int+String).

Two features, however, were tested only against `Int` examples from
`examples/seed_houdini/`, with no Real, String, or combined-theory example
or test anywhere in the repository:

- **`--validate-candidates`** (bounded counterexample-to-induction
  reachability checking, `candidate_validation.py`) and
  **`--dump-promising-candidates`**;
- **`--cands`** (external candidate import, `cands.py`) and `--dump-cands`.

Static review of both modules found no `Int`-specific code (no `IntSort` /
`is_int` branching anywhere; both are built directly on the same
SSA/canonical-variable machinery already proven sort-generic by the Real
and String bounded-exploration test suites), so the gap was believed to be
a testing gap rather than a functional one -- but it was untested, and a
Real+String combination example did not exist at all in either branch of
this repository at the time.

## What was added

| Theory | New/ported example(s) | `--cands` file | Tests |
|---|---|---|---|
| Real | `examples/real_arithmetic/counter_safe.smt2`, `helper_lemma_safe.smt2` | `real_counter_safe_candidates.smt2`, `real_helper_lemma_candidates.smt2` | `test_candidate_validation_theories.py`, `test_cands_theories.py` |
| String | `examples/string_theory/bounded_append_safe.smt2` (ported), `helper_lemma_safe.smt2` | `string_bounded_append_candidates.smt2`, `string_helper_lemma_candidates.smt2` | same |
| Real+String | `examples/mixed_theories/real_string_safe.smt2` (new combination) | `real_string_candidates.smt2` | same |
| Int+Real+String | `examples/mixed_theories/int_real_string_safe.smt2` (new combination) | `int_real_string_candidates.smt2` | same |

Each pairing was constructed so both `--validate-candidates` outcomes are
exercised, not just the happy path:

- **Confirmed real** (`counter_safe.smt2`, `bounded_append_safe.smt2`,
  `real_string_safe.smt2`, `int_real_string_safe.smt2`): a correct
  invariant is supplied alongside a deliberately too-tight candidate that
  is true only at the initial fact. MultiHoudini drops the latter after
  the first transition step, and bounded validation confirms it reachable
  at depth 2.
- **Potentially promising** (`helper_lemma_safe.smt2`, both Real and
  String versions): a single, globally-true candidate is supplied alone,
  deliberately withholding the fact that correlates it with a second state
  component. MultiHoudini's local induction check treats the uncorrelated
  component as unconstrained and manufactures a counterexample-to-induction
  that no real execution can reach; bounded validation correctly reports
  this as promising rather than confirmed, and `--dump-promising-candidates`
  is checked to emit a verification-obligation file with the predicate's
  native (non-Int-coerced) sorts intact.

Three additional String+Int examples (`multiphase_length_transfer_safe.smt2`,
a two-predicate phase transfer; `password_policy_safe.smt2`, regex combined
with a length range; `length_counter_desync_unsafe.smt2`, an unsafe
counterexample) were ported from pyhorn-bounded-explorer 0.0.15's
`examples/string_length_literature/` suite and covered in
`tests/test_string_length_examples.py`, adding parser/bounded-explorer/
seed-Houdini coverage beyond `--cands`/`--validate-candidates` specifically.

## A note on provenance

pyhorn-bounded-explorer 0.0.15 (the source of the ported examples above) is
a **divergent branch**, not a superset of this codebase: it added the
`string_length_literature` benchmark suite but does not include
`candidate_validation.py`, `cands.py`, or the `--cands` /
`--validate-candidates` / `--dump-cands` / `--dump-promising-candidates`
flags at all. The work in this document was done against the branch that
has those features, using 0.0.15 only as a source of additional String+Int
example material.

## Verification caveat

The tests and depth/status values described above were derived by hand --
tracing MultiHoudini's induction-check logic and the relevant satisfiability
questions through `houdini.py` and `candidate_validation.py` line by line --
rather than by executing the test suite, because no environment with Z3
installed was available at the time this work was done. That hand-derivation
was then checked against a real `pytest` run, which is how the two bugs
below were caught.

## Bugs caught by actually running the suite

See also [`docs/set_logic_horn_and_string.md`](set_logic_horn_and_string.md):
bug 2 below (the dumped-file parse failure) turned out to be one instance
of a much broader, pre-existing issue across 30 example files, found by
someone independently testing a file against the real `z3` binary.

Two things the hand-derivation above got wrong, both fixed:

1. **`examples/real_arithmetic/counter_safe.smt2`'s guard.** The first draft
   copied Int's `x < 10` guard literally as `x < 10.0`. Reals are dense, and
   MultiHoudini's induction check for a candidate only has that candidate
   itself -- not the true reachable set -- to characterize the pre-state, so
   with a strict guard it can pick a fractional pre-state such as `x = 9.5`,
   satisfying `x <= 10.0` and the guard, yet stepping to `10.5` and falsely
   refuting an invariant every actual (integer-valued) execution of the loop
   satisfies. `x <= 10.0` was consequently dropped alongside the
   deliberately-weak `x = 0.0`, and the file went to `unknown` instead of
   `Success`. Fixed by tightening the guard to `x <= 9.0` (one step below
   the bound, non-strict), which forces `x + 1.0 <= 10.0` for every real `x`
   satisfying it, not just integers. The equality-based combination examples
   (`real_string_safe.smt2`, `int_real_string_safe.smt2`) were never at risk
   of this: their invariants pin a Real to `to_real` of an inherently
   integer-valued term, so no fractional value can ever satisfy them.
2. **`render_candidate_verification_smt2`'s `(set-logic HORN)`.** This was
   unconditional in `candidate_validation.py`, and Z3's own SMT-LIB2 parser
   rejects the `String` sort under that logic tag -- so a dumped String
   candidate file (`--dump-promising-candidates`) could not be reloaded by
   the very external solver it's meant to be handed to. Fixed by only
   emitting that line when none of the dumped relations need String/RegLan
   sorts (the existing Int-only test, which asserts the line's presence,
   still passes). `tests/test_candidate_validation_theories.py` now
   round-trips both the Real and the String dump through a real
   `z3.Solver().from_string()` call to catch a regression here directly.
3. **`_candidate_variants`' missing regex-complement push (pre-existing,
   not introduced by this round of work, surfaced by a Z3 upgrade).**
   `examples/string_invariant_literature/regex_alphabet_closure_safe.smt2`'s
   query negates `x in Complement(R)`; the correct invariant is `x in R`,
   but `z3.simplify()` does not push negation through a regex complement
   (that is a regex-algebra rewrite, not a propositional one), so
   SeedMiner mined the double-negated `Not(x in Complement(R))` form
   verbatim, alongside `x in R` itself from a separate mining root.

   The first attempt at a fix *added* the pushed form as an extra variant,
   modeled on the numeric-equality case just above it in the same
   function. That was diagnosed as wrong by actually running a standalone
   script against `SeedMiner`/`MultiHoudini` directly (not just guessing
   again): both the un-pushed and pushed forms individually survive
   MultiHoudini's per-candidate induction check fine, so both end up in
   the retained set. The failure isn't in that per-candidate check at all
   -- it's in final certification, which has to verify the *whole*
   retained conjunction against every original rule, and the un-pushed
   form's complement-laden term alone is enough to make that solver call
   time out (`reason: canceled`, not `unsat`/`sat`). A cheaper equivalent
   sitting next to an expensive term doesn't make the expensive term
   cheaper.

   Unlike the numeric-equality variants (where the original and derived
   forms can genuinely differ in inductive strength, so both are worth
   keeping), the regex-complement push carries identical logical content
   to the original -- there's nothing to gain from keeping the un-pushed
   form and, as observed, real cost to it. Fixed by having
   `_candidate_variants` *replace* the un-pushed form with the pushed one
   for this specific shape, rather than appending it. Since `re.comp` is
   used in exactly this one file in the entire corpus, the change cannot
   affect any other example's mined candidates.

   That fix eliminated the complement-laden candidate from the retained
   set entirely (re-diagnosed and confirmed: the retained set is now just
   the one clean `x in R` candidate), but the test *still* failed --
   certification of the append-"b" transition alone was still hitting
   `reason: canceled` at the file's original `timeout_ms=5_000`, with no
   complement anywhere left in the query. That is: `re.comp`'s automaton
   complementation was one genuine cost, now removed, but plain
   regex-closure-under-concatenation is, on its own, apparently more
   expensive for this Z3 version than the `5_000`ms convention used by
   every other regex example in the corpus (union, range, star) budgets
   for. **Correction, found by actually testing it rather than assuming
   it would work:** raising the timeout to `30_000`ms did not fix this.
   Diagnosed further with a standalone script (`diagnose_regex_minimal.py`,
   at the repo root; `diagnose_regex_closure.py`, its earlier and more
   elaborate counterpart, has since been removed as no longer needed): the
   *specific* check that hangs is final certification of
   the query rule itself -- `s in (a|b)*  and  s in Complement((a|b)*)`,
   about as simple as a regex-emptiness check gets -- and it hangs
   identically in complete isolation, bypassing MultiHoudini entirely,
   and on Z3 4.16.0.0 (inside this project's own declared
   `z3-solver>=4.13.0.0,<5` constraint) just as much as on 5.0.0. So this
   is not a version mismatch and not something more mining cleverness or
   more time can route around -- it's a genuine Z3 regex-complement
   performance limit on this specific input. The test
   (`tests/test_string_invariant_literature.py`) was changed to expect
   `HoudiniStatus.UNKNOWN`, joining the other four documented hard cases
   in `docs/string_invariant_literature.md` -- though for a different
   underlying reason (see that doc's section 11.1): SeedMiner finds the
   exact right candidate here, unlike the other four; the solver still
   can't close the resulting check.

   Separately, an attempt was made to demonstrate `--cands` as the escape
   hatch for cases like this: a hand-derived regex for "odd number of W
   symbols" for `coffee_can_odd_white_safe.smt2`
   (`examples/cands/coffee_can_odd_white_candidates.smt2`), exhaustively
   verified as the correct *language* against a brute-force reference
   independent of Z3 (every string of length 0-11 over `{W, B}`, zero
   mismatches). It does not actually reach `Success` -- checked directly,
   not assumed. `--cands` parses it correctly and MultiHoudini never
   rejects it as *wrong* (`removed=0`), but the very first induction
   check attempted (`BB -> B`, which doesn't involve `W` and is
   content-irrelevant to this invariant) times out before certification
   is ever reached. That isolates the cost to checking regex-membership
   invariance across an `x ++ OLD ++ y -> x ++ NEW ++ y` rewrite at an
   existentially-split position, for *any* regex -- not this regex, not
   `W`-counting specifically, and not `re.comp` (the different hard case
   above). Every hard example in `string_invariant_literature/` shares
   this same rewrite shape, so the same wall is expected there too. See
   `test_cands_hand_derived_candidate_also_times_out` in
   `tests/test_candidate_validation_theories.py` and that candidate
   file's own header for the full trace.

This is also the same class of issue as the `(set-logic HORN)` /
Datalog-dialect fix made to the example files themselves in this round:
`set-logic HORN` and String sorts don't mix cleanly in this version of Z3,
in more than one place.
