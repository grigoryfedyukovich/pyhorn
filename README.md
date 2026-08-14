# PyHorn: inductive invariants for linear CHCs

This repository provides Python 3/Z3Py analysis for linear constrained Horn
clauses. Its main strength is **inductive invariant discovery**: a syntactic
SeedMiner followed by multi-predicate Houdini filtering, candidate mutation,
optional user-supplied seeds, and a staged trace-guided candidate generator
that samples concrete bounded models when syntactic mining alone is not
enough. Bounded trace exploration is supporting infrastructure—it powers
reachability checks for candidate validation, supplies models for
trace-guided mining, and remains available as a standalone BMC-style checker.

The primary workflow is Seed-Houdini (and its extensions):

```bash
pyhorn-expl --seed-houdini --print-invariants input.smt2
pyhorn-expl --trace-houdini --trace-depth 8 --print-invariants input.smt2
```

`Success` is reported only when the conjunction of candidates retained for each
predicate makes **every** normalized fact, transition, and query CHC valid under
independent, fresh-solver certification. `unknown` means either that a query
remains satisfiable under the retained candidates or that Z3 returned
`unknown`; it is not a claim that the input is unsafe.

When invariant search returns `unknown`, or when you want a concrete
counterexample rather than an inductive certificate, the same binary runs
**bounded verification**: exhaustive ENTRY-to-error trace exploration up to a
chosen depth (`--upto`), with optional models and SMT dumps. That path is
described briefly under [Installation](#installation) and in full under
[Bounded exploration](#bounded-exploration-supporting-engine).

```bash
# Search for a counterexample within a bound (BMC-style)
pyhorn-expl --upto 20 --model input.smt2
```

## Supported input formats

Both common CHC encodings are supported.

### Z3 fixedpoint command syntax

```smt2
(declare-var x Int)
(declare-rel inv (Int))
(declare-rel fail ())
(rule (inv 0))
(rule (=> (and (inv x) (< x 2)) (inv (+ x 1))))
(rule (=> (and (inv x) (>= x 2)) fail))
(query fail)
```

### Pure SMT-LIB HORN assertions

```smt2
(set-logic HORN)
(declare-fun inv (Int) Bool)
(assert (inv 0))
(assert
  (forall ((x Int))
    (=> (and (inv x) (< x 2))
        (inv (+ x 1)))))
(assert
  (forall ((x Int))
    (=> (and (inv x) (>= x 2))
        false)))
(check-sat)
```

For pure SMT-LIB input, a clause ending in `false` is treated as an error
clause. An interpreted safety head is also supported. For example,
`(assert (forall ((x Int)) (=> (inv x) (<= x 1))))` is checked by exploring
states satisfying `inv(x)` and the negation of the asserted property.

The supported fragment is **linear CHC**: a rule body may contain at most one
positive relation application. Nonlinear clauses are rejected with an explicit
diagnostic. Integer, real, string, regular-expression, array, bit-vector,
Boolean, and retained nested-quantifier constraints are represented directly
by Z3 expressions.

### Real arithmetic

`Real` is supported throughout parsing, SSA construction, bounded solving,
SeedMiner, MultiHoudini, model output, and SMT dumping. SMT-LIB decimal and
fractional literals have Z3's exact mathematical-real semantics: `0.1` is the
exact rational `1/10`, not an IEEE floating-point approximation.

Supported real-arithmetic patterns include:

- linear `+`, `-`, comparisons, equality, and multiplication by constants;
- exact division with `/`;
- strict and non-strict real inequalities;
- mixed `Int`/`Real` state using SMT-LIB/Z3 `to_real` coercions;
- arrays whose index or element sorts include `Real`;
- quantified formulas over real variables; and
- nonlinear real formulas, which are passed to Z3 and may return `unknown`
  under a timeout.

Integer `div` and `mod` retain their SMT-LIB integer semantics; use `/` for
real division. PyHorn does not convert mathematical reals to Python floats.

Examples are under [`examples/real_arithmetic/`](examples/real_arithmetic/),
with the precise support contract in
[`docs/real_arithmetic.md`](docs/real_arithmetic.md).

### Strings and regular expressions

SMT-LIB `String` is supported in both CHC syntaxes and is preserved as Z3's
native Unicode string/sequence theory. The tested contract includes:

- string equality and disequality;
- `str.++`, `str.len`, `str.at`, and `str.substr`;
- `str.prefixof`, `str.suffixof`, and `str.contains`;
- `str.indexof` and `str.replace`;
- `str.to_int` and `str.from_int` combined with integer state;
- regular-expression membership with `str.in_re`, `str.to_re`, and `re.*`;
- mixed `String`/`Int` predicate signatures; and
- arrays whose index or element sorts include `String`.

String constraints are sent directly to Z3. Difficult combinations of strings,
length arithmetic, regular expressions, and quantifiers may return conservative
`unknown` under the configured per-check timeout. SMT-LIB Unicode escapes such
as `"\u{3bb}"` are preserved; no byte-string encoding is introduced by
PyHorn.

Examples are under [`examples/string_theory/`](examples/string_theory/), with
the detailed contract in [`docs/string_theory.md`](docs/string_theory.md).

### Combining Real and String

The Real and String examples above each combine with `Int`, but not with
each other directly. [`examples/mixed_theories/`](examples/mixed_theories/)
covers that pairing explicitly, with a Real+String example and a three-way
Int+Real+String example -- plus one this tool cannot solve, an Int+String
problem whose safety argument needs a modular/parity invariant that
syntactic candidate mining cannot express (see that directory's README).


## Installation

```bash
python3 -m pip install .
```

This installs both command names (`pyhorn-expl` and `chc-bounded-explorer`).
Typical invocations:

```bash
# Inductive invariants (main strength)
pyhorn-expl --seed-houdini --print-invariants input.smt2
pyhorn-expl --trace-houdini --trace-depth 8 --print-invariants input.smt2

# Bounded verification / counterexample search (when invariants return unknown)
pyhorn-expl --upto 20 --model input.smt2
chc-bounded-explorer --upto 20 input.smt2
```

It can also be run directly without installation:

```bash
python3 bounded_explorer.py --seed-houdini examples/seed_houdini/counter_safe.smt2
python3 bounded_explorer.py --upto 20 examples/assert_syntax.smt2
```


## SeedMiner and MultiHoudini

Run the complete candidate-mining and invariant-filtering pipeline with:

```bash
pyhorn-expl --seed-houdini input.smt2
```

The default human-readable output is deliberately just one of:

```text
Success
```

or:

```text
unknown
```

`Success` is reported only when the conjunction of candidates retained for each
predicate makes **every** normalized fact, transition, and query CHC valid.
`unknown` means either that a query remains satisfiable under the retained
candidates or that Z3 returned `unknown`; it is not a claim that the input is
unsafe.

Print the retained predicate annotations and diagnostics with:

```bash
pyhorn-expl \
  --seed-houdini \
  --print-invariants \
  --debug \
  input.smt2
```

Use `--json` for candidate, filtering, and failure statistics.

### Candidate mining

SeedMiner creates canonical typed variables for every non-query predicate and
observes the normalized Z3 parse tree of every CHC. It mines:

- Boolean subtrees, splitting conjunctions while preserving disjunctions;
- complete negated query bad-state patterns;
- repeated, constant, and nontrivial relation-argument structure;
- both one-sided arithmetic bounds implied by numeric equality;
- universally closed query candidates when bad-state witnesses are rule-local;
- candidates transferred across pure predicate-renaming/permutation rules.

Candidates remain native Z3 ASTs, including arrays, bit-vectors, Booleans,
arithmetic, `select`, `store`, and quantifiers. Every accepted candidate is
predicate-local; noncanonical free variables are rejected.

This remains a syntactic candidate language. It does not yet synthesize general
affine combinations, modular/path-sensitive invariants, polynomial templates,
or the original implementation's full array range/access grammar. These limits
reduce completeness but cannot make a certified answer unsound. `--mut` (below)
closes part of this gap -- specifically, linear combinations of equalities and
transitive chains of inequalities -- without attempting the rest.

### Candidate mutation (`--mut`)

`--mut` derives additional candidates from whatever's already in the pool --
seed-mined, `--cands`-supplied, or both merged together -- by combining pairs
of numeric equalities and inequalities within each relation's own candidate
set. Ported from and extends FreqHorn's `RndLearnerV3.hpp::mutateHeuristicEq`:

- **Equalities** (ported as-is): given `L1 = R1` and `L2 = R2` already in the
  pool, both `(L1+L2) = (R1+R2)` and `(L1-L2) = (R1-R2)` hold, and so do the
  same after swapping the second equality's sides (since `L2 = R2` iff
  `R2 = L2`): `(L1+R2) = (R1+L2)` and `(L1-R2) = (R1-L2)`. Four derived
  candidates per unordered pair.
- **Inequalities** (new): given `L1 <=/< R1` and `L2 <=/< R2` (`>=`/`>` are
  normalized to this form first), if `R1` is syntactically the same term as
  `L2`, the chain `L1 <=/< R2` holds -- strict if either input was. This is
  transitivity: `x <= y` and `y <= z` give `x <= z`; `x < y` and `y <= z`
  give `x < z`.

Results that simplify to `True`/`False`, or that duplicate a candidate
already present, are dropped. Nothing here reasons across two different
predicates' candidate sets, and it runs once (derived candidates are not
themselves re-mutated). Requires `--seed-houdini` or `--cands` (or, with
`--trace-houdini`, is supported directly there instead); combine with any
of those. Not ported from the original: a narrower constant-multiple
substitution pass (turning `x = 5` and `y = 10` into `y = 2*x`), left for a
future extension if needed.

```bash
pyhorn-expl --cands examples/cands/transitive_bounds_candidates.smt2 --mut \
  --debug --print-invariants \
  examples/seed_houdini/transitive_bounds_safe.smt2
```

`--debug` reports `Mutation: equalities=N, inequalities=N, eq-pairs=N,
ineq-chains=N, added=N`, and `--json` includes the same counts under a
top-level `"mutation"` key. Note that Z3's own linear-arithmetic reasoning
already combines simultaneously-retained hypotheses like `x<=y` and `y<=z`
for free during final certification, so `--mut` is not usually *necessary*
for a single relation's own certification to succeed -- what it adds is
making the combined fact (`x<=z`) a first-class, independently-retained
candidate, which matters when a later rule or a different predicate needs
exactly that fact and not its ingredients (e.g. after a multi-predicate
transition that carries `x` and `z` forward but drops `y`).

`--mut` also derives candidates beyond the numeric pairing above, none of
it limited to arithmetic:

- **Sort-agnostic equality substitution.** Given any equality `a = b`
  already in the pool -- Int, Real, String, Array, Bool, BitVec, anything
  -- every other candidate `c` is rewritten by substituting `b` for `a`
  and `a` for `b`. Sound for free (any model satisfying `a = b` and `c`
  also satisfies the rewritten formula), and it subsumes many per-theory
  bridge rules (length facts under string equality, select facts under
  array equality) as special cases rather than needing one hand-written
  rule per theory pair.
- **Explicit String bridges.** `s1 = s2` → `str.len(s1) = str.len(s2)`;
  `str.prefixof`/`str.suffixof`/`str.contains` against a concrete literal →
  a length lower bound; `u = str.++(s, t)` → `str.len(u) = str.len(s) +
  str.len(t)`, plus literal propagation through the concatenation --
  `u = "abcd"` when every operand resolves to a literal, or the weaker
  `str.prefixof("ab", u)` when only a leading run does.
- **Regex intersection.** Two membership facts `InRe(s, R1)` and
  `InRe(s, R2)` on the same subject become `InRe(s, Intersect(R1, R2))`;
  Z3's own regex simplifier decides whether that's tighter than either
  input. Deliberately *not* extended to regex complement -- this
  codebase's own benchmarks have a documented history of Z3 hanging on
  complement-heavy checks (see
  [`docs/candidate_validation_theory_coverage.md`](docs/candidate_validation_theory_coverage.md)),
  so proposing more complement-shaped candidates isn't worth the risk.

`--debug` prints a second `Mutation (bridges): ...` line covering these
(only when at least one of them found something to do), and `--json`'s
`"mutation"` key gains `general_equalities_considered`,
`substitution_rewrites_attempted`, `substitution_candidates_added`,
`string_bridges_emitted`, `regex_memberships_considered`, and
`regex_pairs_intersected` alongside the existing numeric-pairing counts.

### MultiHoudini filtering

MultiHoudini accepts one candidate set per predicate. It lazily creates one
persistent filtering solver for each relevant non-query CHC. Source candidates
are guarded by assumption literals. The active destination violation is added
in a balanced temporary scope:

```text
rule body
and active source candidates
and some active destination candidate is false
```

A satisfiable check removes every destination candidate falsified by the model.
If Z3 does not concretely evaluate a quantified candidate, PyHorn checks active
destination candidates individually under the same source assumptions. A Z3
`unknown` or unattributable SAT result produces conservative `unknown`, not an
internal failure.

After filtering reaches a fixed point, **every original CHC is reconstructed
and checked in a fresh solver**. Query clauses participate in this independent
certification. `Success` is returned only if all certification obligations are
UNSAT.

Focused safe, unsafe, array, multiple-predicate, and original-corpus corner cases
are under `examples/seed_houdini/` and `examples/freqhorn_corner_cases/`.

### Counterexamples to induction

Every candidate MultiHoudini removes is removed because some concrete model
falsified it -- a counterexample to induction (CTI): a transition of one CHC
rule from a pre-state to a post-state under which the candidate does not
hold. `--debug` prints each one to stderr as it happens, separate from the
`Success`/`unknown` result on stdout:

```text
Dropped candidates (4):
  dropped r0[r0: ENTRY -> inv] inv: (not (<= __inv_0 10))
    pre:  (fact -- no source predicate)
    post: __inv_0 = 0
  dropped r1[r1: inv -> inv] inv: (= 0 __inv_0)
    pre:  __inv_0 = 0
    post: __inv_0 = 1
  ...
```

`pre` is the source predicate's canonical variables evaluated in the
countermodel, `post` is the destination predicate's; `pre` is omitted for
fact rules, which have no source predicate. `--json` always includes the
full set under `removed_candidates`, each with `relation`, `candidate`
(the dropped s-expression), `rule_id`, `rule`, `pre_state`, `post_state`,
and `full_model` (the complete `str(z3.ModelRef)`, useful for array or
uninterpreted-sort variables the `pre`/`post` summary doesn't otherwise
show). This applies equally whether the candidates came from
`--seed-houdini`, `--cands`, or both.

#### Bound-checking removed candidates (`--validate-candidates`)

A candidate MultiHoudini removes is refuted by a countermodel of the
*local* transition relation -- a counterexample to induction (CTI): one
satisfying assignment of `source_candidates(src_args) AND rule.body AND
NOT candidate(dst_args)`, picked by whichever solver run happened to find
it. That is real in the sense that the candidate genuinely is not inductive
as stated, but the CTI itself says nothing about whether an actual
unrolling of the program from the start can ever falsify the candidate --
and any variable the active candidate set does not constrain (a loop
counter no retained candidate mentions, say) gets an arbitrary,
solver-chosen value in it, one that can differ across otherwise-equivalent
runs purely because a *different* candidate set changed what the solver
happened to explore, even though the same candidate is refuted identically
either way. So `--validate-candidates` does not check reachability of the
CTI -- it checks reachability of **the candidate**: does some real,
bounded execution of the program reach the candidate's own relation in a
state where the candidate does not hold, via any rule sequence that can
produce it, not just whichever one rule the CTI happened to come from? That
is a property of the candidate, existentially quantified over everything
else, not of any one witness -- which is what keeps the verdict independent
of which other candidates happened to be active and which specific rule the
countermodel came from.

`--validate-candidates` runs this the same way `chc-bounded-explorer`
itself checks query reachability: incremental unrolling from the start, one
additional step at a time, up to `--candidate-bound` steps (default 10). If
some trace reaches a falsifying state, the removal is confirmed; if not
within the bound, the candidate is flagged as potentially promising
instead. This is exactly the same question `--dump-promising-candidates`'s
generated file asks in full, unbounded generality via `forall`; this is the
bounded version, for a quick, incremental first check.

```bash
pyhorn-expl --seed-houdini --validate-candidates --debug examples/seed_houdini/counter_safe.smt2
```

```text
Dropped candidates (4):
  dropped r0[r0: ENTRY -> inv] inv: (not (<= __inv_0 10))
    pre:  (fact -- no source predicate)
    post: __inv_0 = 0
    check: confirmed real (base case, always reachable)
  dropped r1[r1: inv -> inv] inv: (= 0 __inv_0)
    pre:  __inv_0 = 0
    post: __inv_0 = 1
    check: confirmed real (falsified by a reachable state at depth 2)
  ...
```

Depth counts steps to reach the candidate's relation *in the falsifying
state itself*, not steps to reach the CTI's pre-state: `x = 0` is falsified
once `inv` holds `x = 1`, one self-loop step after the fact that
established `x = 0`, hence depth 2. The `pre`/`post` lines still show that
CTI, purely for reading -- they are not what `--validate-candidates` itself
checks (see above).

A candidate that is true but not locally inductive on its own reads
differently -- for example `y >= 1` supplied alone for a loop that keeps
`y == 100 - x` invariant, without also supplying that correlating fact:

```text
  dropped r1[r1: inv -> inv] inv: (>= __inv_1 1)
    pre:  __inv_0 = 0, __inv_1 = 1
    post: __inv_0 = 1, __inv_1 = 0
    check: potentially promising (no falsifying state found within 10 steps -- may need a helper lemma)
```

"Not found within the bound" is not a proof: a longer trace might still
falsify the candidate, and `--candidate-bound` trades off search depth
against how quickly the check returns -- raise it if a "promising" verdict
might just be one or two steps short (as with any bounded check, a
candidate genuinely requiring depth *d* to falsify reads as promising at
any bound below *d*). `--json` includes the same verdict under each removed
candidate's `candidate_validation` (`status`, `checked_upto`,
`witness_depth`, `checks_performed`, `elapsed_seconds`, `reason_unknown`),
or `null` when `--validate-candidates` was not passed.
`--validate-candidates` requires `--seed-houdini` and/or `--cands`, same as
`--dump-cands`.

#### Externally verifying promising candidates (`--dump-promising-candidates`)

A `not-found` verdict is a hint, not a proof -- confirming it one way or the
other calls for a stronger or simply different check than the bounded
search `--validate-candidates` itself runs. `--dump-promising-candidates DIR`
writes one standalone SMT-LIB2 file per `not-found` candidate into `DIR`
(created if missing): every transition rule of the original program,
unchanged, with the original safety property replaced by a direct question
-- does *this* candidate hold for every reachable state of its relation?

```bash
pyhorn-expl --cands weak_cands.smt2 --validate-candidates \
  --dump-promising-candidates candidates_out --debug input.smt2
```

```text
Dropped candidates (1):
  dropped r1[r1: inv -> inv] inv: (>= __inv_1 1)
    pre:  __inv_0 = 0, __inv_1 = 1
    post: __inv_0 = 1, __inv_1 = 0
    check: potentially promising (no falsifying state found within 10 steps -- may need a helper lemma)
    file: candidates_out/inv__r1__61b8aafd37.smt2
```

```smt2
; Externally-checkable verification task generated by chc-bounded-explorer --dump-promising-candidates.
; Original program: input.smt2
; Candidate: (>= __inv_1 1)
; Originally proposed for relation: inv
; Removed by rule r1 [r1: inv -> inv]
; Not found reachable within 10 step(s) (10 check(s) tried).
; This file reuses every transition rule from the original program verbatim, replacing the original safety property with a direct check of whether the candidate above holds for every reachable state of its relation.

(set-logic HORN)

(declare-fun inv (Int Int) Bool)

(assert (inv 0 100))
(assert (forall ((__pyhorn_r1_0_0_x Int) (__pyhorn_r1_0_1_y Int)) (=> (and (inv __pyhorn_r1_0_0_x __pyhorn_r1_0_1_y) (not (<= 5 __pyhorn_r1_0_0_x))) (inv (+ __pyhorn_r1_0_0_x 1) (- __pyhorn_r1_0_1_y 1)))))

(assert (forall ((__inv_0 Int) (__inv_1 Int)) (=> (inv __inv_0 __inv_1) (>= __inv_1 1))))

(check-sat)
```

The generated file is ordinary input this tool can read back: re-run it with
a larger, unbounded-feeling `--upto` for a deeper BMC-style search than
`--candidate-bound` defaults to, hand it to `--seed-houdini` for an
independent, fresh invariant-mining attempt, or feed it to any other
HORN-capable solver entirely outside this tool. It never references the
original query relation -- the whole point is a clean, isolated question
about one candidate, not the original property. `--dump-promising-candidates`
requires `--validate-candidates` (there is nothing to classify as promising
without it); filenames are content-derived (relation, rule, and a short hash
of the candidate) so re-running on an unchanged program overwrites the same
files instead of accumulating stale ones. `--json`'s `removed_candidates`
entries include the written path under `verification_file` (`null` when not
written).

### User-supplied candidates (`--cands`)

`--seed-houdini` mines its own candidates syntactically. `--cands FILE`
instead lets you hand MultiHoudini your own guesses, skipping (or
supplementing) the miner entirely:

```bash
pyhorn-expl --cands mycands.smt2 --print-invariants input.smt2
```

`FILE` is an ordinary SMT-LIB2 file containing one or more `define-fun`
commands, at most one group per uninterpreted, non-query predicate:

```smt2
(define-fun inv ((x Int) (n Int)) Bool
  (and (>= x 0) (<= x n)))
```

Each `define-fun` is parsed by Z3, its parameters are bound directly to the
predicate's own canonical variables (positionally -- the parameter *names* in
the file are unrelated to any name used internally or in the target CHC
file), and the resulting formula is split into separate conjuncts at every
top-level `and`. MultiHoudini then removes exactly the conjuncts that are not
inductive, the same way it treats mined candidates, and reports `Success`
only if every retained conjunct, for every predicate, survives fresh
certification. Multiple `define-fun`s for the same predicate are merged;
`declare-fun`, `set-logic`, and comments are accepted and ignored, so the same
file may double as documentation.

`--cands` implies Houdini mode on its own (no `--seed-houdini` required) and
disables slicing, exactly like `--seed-houdini`. Combine both flags to merge
mined and user-supplied candidates before filtering:

```bash
pyhorn-expl --seed-houdini --cands mycands.smt2 --print-invariants input.smt2
```

A predicate absent from `FILE` simply starts Houdini with its default `true`
invariant, as if you had supplied no candidates for it at all. A
`define-fun` whose name does not match any predicate in the CHC file (a typo,
or a query/error relation) is silently skipped, matching ordinary SMT-LIB2's
tolerance of extraneous declarations. Parameter-count mismatches and
non-`Bool` return sorts are hard errors.

Worked examples matching the benchmarks under `examples/seed_houdini/` are in
`examples/cands/`:

```bash
pyhorn-expl --cands examples/cands/counter_safe_candidates.smt2 \
  --print-invariants examples/seed_houdini/counter_safe.smt2
```

`examples/cands/` also has Real, String, Real+String, and Int+Real+String
worked examples pairing a correct invariant with a deliberately too-tight
candidate, exercising `--cands` and `--validate-candidates` (below) across
theories -- see
[`docs/candidate_validation_theory_coverage.md`](docs/candidate_validation_theory_coverage.md)
for a summary and the corresponding files. If you're loading any example
file directly with a standalone `z3` binary rather than through this
tool, see
[`docs/set_logic_horn_and_string.md`](docs/set_logic_horn_and_string.md)
first -- `(set-logic HORN)` and `String` don't mix in this version of Z3.

#### Saving and replaying candidates (`--dump-cands`)

`--print-invariants` prints Python's infix form (`__inv_0 <= 10`) for quick
inspection; that text is not valid SMT-LIB2 and cannot be fed back through
`--cands`. `--dump-cands FILE` instead writes the retained candidates as
proper `define-fun` s-expressions, so a mining run's output can be replayed
without re-mining, hand-edited, or checked into version control:

```bash
# Mine once, save what MultiHoudini kept:
pyhorn-expl --seed-houdini --dump-cands mined.smt2 input.smt2

# Replay later -- no mining, just filtering the saved candidates:
pyhorn-expl --cands mined.smt2 input.smt2
```

`--dump-cands` requires `--seed-houdini` and/or `--cands` (there is nothing
to dump otherwise) and writes its output regardless of the final status, so
an `unknown` run still leaves behind whatever partial candidate set
MultiHoudini ended up with, for inspection or as a starting point for manual
editing. Round-tripping through `--dump-cands` then `--cands` reproduces the
original status exactly, since nothing in the dumped file needs to be
removed again.

To check that property holds for a CHC file of your own (not just the two
examples `tests/test_cands_roundtrip.py` ships with), either run the two
commands above by hand and compare their output, or point the existing
round-trip test at it:

```bash
PYHORN_ROUNDTRIP_FILE=/path/to/your.smt2 \
  python3 -m pytest tests/test_cands_roundtrip.py -k custom_file -v
```

This asserts the `--seed-houdini` → `--dump-cands` → `--cands` status is
stable (`Success` stays `Success`, `unknown` stays `unknown`) and that
nothing is removed on replay. The test is skipped, not run, when
`PYHORN_ROUNDTRIP_FILE` is unset, so it is a no-op in ordinary `pytest -q`
runs and in CI -- the same convention `PYHORN_BENCH_HORN_DIR` uses for the
external corpus regression.

### Trace-guided candidate generation (`--trace-houdini`)

`--seed-houdini`, `--cands`, and `--mut` all propose candidates from what is
already *syntactically present* in the CHCs (or supplied by hand). Some
invariants -- a modular length relation, an affine relation between two
predicate arguments -- are never written down anywhere in the input, only
implied by it. `--trace-houdini` samples concrete bounded reachable states
along the way (the same SSA machinery bounded exploration uses) and
generalizes them into candidates from a closed registry of 15 template
families (constants, one- and two-sided numeric bounds, integer congruence,
affine equality, and eight string templates):

```bash
pyhorn-expl --trace-houdini --trace-depth 8 input.smt2
```

It is staged and monotonic with respect to `--seed-houdini`: an ordinary
Seed-Houdini attempt runs first, and trace sampling is only invoked -- and
only spends its budget -- if that baseline does not already prove the
program. A trace-mined candidate is exactly as untrusted as any other:
MultiHoudini filters the combined candidate set and every original CHC is
independently certified by a fresh solver, same as every other mode above.

```bash
pyhorn-expl \
  --trace-houdini \
  --trace-depth 8 \
  --trace-limit 1000 \
  --trace-models-per-prefix 2 \
  --trace-samples-per-predicate 64 \
  --trace-candidates-per-predicate 256 \
  --debug --print-invariants --json \
  input.smt2
```

Inspect the complete, stable template registry without an input file:

```bash
pyhorn-expl --list-trace-templates
pyhorn-expl --list-trace-templates --json
```

This is a separate top-level mode from `--cands` in this release -- it
cannot yet be combined with `--cands`, `--validate-candidates`,
`--dump-cands`, or `--dump-promising-candidates`. `--mut` *is* combinable,
and applies to the full combined seed-plus-trace candidate set at whichever
stage the pipeline reaches. `--seed-houdini` may be passed alongside it too,
but has no separate effect, since this pipeline already runs an ordinary
seed-houdini attempt as its own first stage:

```bash
pyhorn-expl --trace-houdini --mut --debug --print-invariants input.smt2
```

Trace-sampled candidate pools can carry far more numeric equalities than
the syntactically-mined pools `--mut` was originally sized for -- pairing
cost is quadratic in that count, and substitution's is linear in
candidates × equalities -- so `--trace-houdini --mut` caps how many
equalities and how many inequalities (independently, per predicate) are
drawn from the combined pool before numeric pairing *and* how many feed
equality substitution, all via `--trace-mutation-limit`, defaulting to 32.
A separate `--trace-mutation-substitution-limit` (default 256) caps
substitution's own rewrite-attempt budget, independent of how many
equalities fed it -- the two together bound cost from both sides. Lower
either for a faster but less thorough mutation pass, raise for more
thorough but slower, or set to `0` to disable that particular cap and
match `--mut`'s own unbounded behavior outside `--trace-houdini`.
`--debug`/`--json` report how many terms and how many substitution
attempts each cap dropped, if any.

Worked examples are under
[`examples/trace_houdini/`](examples/trace_houdini/) and
[`examples/string_length_literature/`](examples/string_length_literature/);
the full design, template language, and current evaluation are in
[`docs/trace_model_generalization.md`](docs/trace_model_generalization.md)
and [`docs/trace_candidate_templates.md`](docs/trace_candidate_templates.md).

Both `SeedMiner` and `TraceCandidateMiner` implement a small, neutral
`CandidateGenerator` extension API (`generator_id` + `generate() ->
CandidateBatch`, merged via `merge_candidate_batches`) intended for future
proposal engines -- statistical, learned, or otherwise -- without changing
MultiHoudini or the certification boundary; see
[`docs/candidate_generator_api.md`](docs/candidate_generator_api.md).


## Bounded exploration (supporting engine)

The bounded explorer is the engine used internally by `--trace-houdini` and
`--validate-candidates`, and is available standalone for short counterexamples
and replayable unrollings. It:

1. parses a linear constrained Horn-clause system with Z3;
2. normalizes every clause into a typed `HornProgram` / `HornRule` database;
3. enumerates all ENTRY-to-error traces exhaustively in increasing length;
4. converts each trace to an SSA verification condition using native Z3 ASTs;
5. caches deterministic `(rule_id, step_index)` SSA instances in a bounded LRU cache;
6. optionally dumps every checked trace as a compact, replayable
   `bnd/expl`-compatible SMT-LIB2 unrolling;
7. checks traces either with a cross-trace incremental solver pool or with the
   original fresh-solver-per-trace baseline; and
8. caches infeasible rule prefixes to prune every longer trace that begins with
   one of them.

```bash
pyhorn-expl --upto 20 input.smt2
python3 bounded_explorer.py --upto 20 examples/assert_syntax.smt2
```

## Solver modes

The default mode is a cross-trace incremental pool retaining at most 16
solver contexts:

```bash
pyhorn-expl --solver-mode pool --max-solvers 16 --upto 20 input.smt2
```

The explicit `--max-solvers 16` above matches the default and is shown to make
the experimental configuration visible. Set another positive value to change
the memory/reuse tradeoff, or use `--max-solvers 0` for an intentionally
unbounded pool.

Each retained solver represents a rule prefix whose SSA constraints have already
been proved satisfiable. For a new trace, the explorer finds the retained solver
with the longest common rule prefix, pops its divergent suffix, and pushes and
checks the new suffix.

The original baseline is available explicitly:

```bash
pyhorn-expl --solver-mode fresh --upto 20 input.smt2
```

`fresh` mode has the following precise behavior:

- creates one new `z3.Solver` for every candidate trace;
- adds SSA constraints monotonically, one trace step at a time;
- calls `check()` after each addition to identify the first infeasible prefix;
- never calls `push()` or `pop()`;
- retains no solver assertions or learned solver state across traces.

Both modes use the same parser, normalized rules, trace order, SSA cache, SMT
dumps, and infeasible-prefix pruning. Therefore, comparing these two commands
isolates the effect of cross-trace solver reuse:

```bash
pyhorn-expl \
  --solver-mode pool \
  --random-seed 1 \
  --upto 100 \
  --json \
  input.smt2 > pool.json

pyhorn-expl \
  --solver-mode fresh \
  --random-seed 1 \
  --upto 100 \
  --json \
  input.smt2 > fresh.json
```

For controlled timing experiments, run each mode several times in separate
processes and compare at least:

- total wall-clock time;
- `solvers_created`;
- `checks`;
- `pushes` and `pops`;
- `common_prefix_steps_reused`;
- SSA cache hits and misses.

In fresh mode, `pushes`, `pops`, and retained `contexts` are always zero, while
`solvers_created` equals the number of traces actually checked.


## Important options

- `--from N`: first trace length, default `1`;
- `--upto N`: maximum trace length, default `10000`;
- `--to MS`: timeout for each Z3 check, default `1000` ms;
- `--debug`: print normalized rules and per-depth statistics;
- `--json`: produce machine-readable output;
- `--model`: print a counterexample model;
- `--seed-houdini`: run SeedMiner, MultiHoudini, and final CHC validation instead
  of bounded trace exploration;
- `--print-invariants`: print retained candidates in `--seed-houdini` /
  `--cands` / `--trace-houdini` mode;
- `--trace-houdini`: run staged trace-guided candidate generation (see
  above) instead of, or as a fallback beyond, plain `--seed-houdini`;
- `--list-trace-templates`: print the trace-generalization template
  registry and exit, without requiring an input file;
- `--dump-vc FILE`: save only the decisive SAT/unknown trace VC as SMT-LIB;
- `--dump-smt DIR`: save every checked trace as a compact SMT-LIB2 unrolling
  using the original `bnd/expl` filename and file format. Existing directories
  are allowed;
- `--solver-mode {pool,fresh}`: select the solver backend, default `pool`;
- `--solver-reuse-min-ratio R`: in pool mode, reuse the best solver only when
  its common prefix is longer than `R * trace_length`; the default is `1/3`;
- `--max-solvers N`: in pool mode, cap retained solver contexts and reset/reuse
  the least recently used solver when necessary. The default is `16`; `0`
  intentionally disables the limit;
- `--max-ssa-cache-steps N`: cap cached SSA steps and state versions. The
  default is `65536`; `0` intentionally disables the limit;
- `--skip-elim`: retain rules outside the semantics-preserving ENTRY-to-query
  graph slice.

Exit codes are `0` for bounded/complete safety or seed-Houdini `Success`, `1`
for a bounded counterexample, `2` for `unknown`, and `3` for input or usage
errors.

### Dump checked unrollings in `bnd/expl` format

```bash
python3 bounded_explorer.py \
  --upto 10 \
  --dump-smt unrollings \
  examples/bench_horn_multiple/abdu_05.smt2
```

The filename is derived from the input benchmark, bound, trace number, and Z3
result:

```text
abdu_05_k3_unsat.smt2
abdu_05_k4_t1_unsat.smt2
abdu_05_k4_t2_unsat.smt2
...
abdu_05_k10_t8_unsat.smt2
```

The `_tN` component is omitted when a bound has only one candidate trace. When
a bound has multiple candidates, `N` is the one-based position in the complete
trace list generated for that bound, matching the C++ explorer. The final suffix
is `_sat`, `_unsat`, or `_unknown`.

Each file is written after the corresponding Z3 check and has the compact form:

```smt2
; bnd/expl SMT dump
; bound: 3
; result: unsat

(declare-fun __bnd_var_0 () Int)
...
(assert (and ...))
(check-sat)
```

There is exactly one conjunctive `(assert ...)`. State versions use
`__bnd_var_N`, while rule-local symbols use `__loc_var_N`. The internal solver
may use a more explicit cached SSA representation, but the dumped formula is
equisatisfiable and follows the compact C++ convention. Existing files with the
same generated name are replaced; unrelated files in the directory are kept.

`abdu_05.smt2` is included as a worked example of this format. Cross-checking
its output against the 36 C++ reference dumps is not part of the bundled test
suite, since those reference files are not included in this checkout.


## Incremental solver-pool reuse

In `pool` mode, the explorer:

1. indexes retained contexts by the first rule of the new trace;
2. chooses the context in that bucket with the longest common prefix;
3. reuses it when the prefix passes the configured ratio threshold;
4. calls `pop()` once per divergent old step;
5. calls `push()`, `add()`, and `check()` for every new suffix step.

A newly unsatisfiable or `unknown` step is popped immediately, so every stored
context remains a known-SAT prefix. If no context is a useful fit, a new solver
is created until the configured limit is reached. The default limit is 16.
After that, the least recently used context is reset and its existing physical
Z3 solver object is reused, bounding retained native solver memory.

The `--debug` output reports the selected solver mode, configured pool limit,
solvers created, recycled contexts, retained contexts, reused prefix steps,
pushes, pops, checks, and SSA-cache size/hits/misses/evictions. The same counters,
`solver_mode`, and `max_contexts` are included in `--json` output.


## Python API

The default API uses the solver pool:

```python
from pyhorn_bnd import BoundedExplorer, parse_chc_file

program = parse_chc_file("input.smt2")
result = BoundedExplorer(
    program, solver_mode="pool", max_solver_contexts=16
).explore(upto=100)
```

Use the baseline backend with:

```python
result = BoundedExplorer(program, solver_mode="fresh").explore(upto=100)
```

The seed-Houdini API is:

```python
from pyhorn_bnd import parse_chc_file, run_seed_houdini

program = parse_chc_file("input.smt2", slice_program=False)
result = run_seed_houdini(program, timeout_ms=1000, random_seed=1)
print(result.status.value)
```

For controlled experiments with explicit candidate sets, use `SeedMiner` and
`MultiHoudini` separately:

```python
from pyhorn_bnd import MultiHoudini, SeedMiner

seeds = SeedMiner(program).mine()
result = MultiHoudini(program, seeds.variables).run(seeds.candidates)
```

To supply your own candidates (optionally merged with mined ones) instead of
going through the CLI:

```python
from pyhorn_bnd import (
    MultiHoudini,
    SeedMiner,
    merge_candidate_maps,
    parse_candidate_file,
)

miner = SeedMiner(program)  # miner.variables is ready without calling .mine()
user_candidates = parse_candidate_file("mycands.smt2", miner.variables)
result = MultiHoudini(program, miner.variables).run(user_candidates)

# Or merge with mined candidates:
seeds = miner.mine()
merged = merge_candidate_maps(seeds.candidates, user_candidates)
result = MultiHoudini(program, miner.variables).run(merged, seed_result=seeds)
```

`format_candidates_smt2` is the inverse of `parse_candidate_file` -- it
renders a `CandidateMap` back as `define-fun` text (what `--dump-cands`
writes):

```python
from pyhorn_bnd import format_candidates_smt2

dump_text = format_candidates_smt2(result.candidates, miner.variables)
```


## Literature-derived string invariant benchmarks

The repository includes nine nontrivial CHC examples under
`examples/string_invariant_literature/`. They cover regular model checking,
word-rewrite systems, character-parity arguments, sanitizers, and relational
string-copy loops.

Run their parser and solver regressions with:

```bash
python3 -m pytest -q tests/test_string_invariant_literature.py
```

Audit every example with both Seed-Houdini and bounded exploration:

```bash
PYTHONPATH=src python3 tools/audit_string_invariant_benchmarks.py \
  --timeout 2000 --bounded-depth 6 --json
```

The current baseline certifies the regex-closure, sanitizer, and copy examples;
finds bounded counterexamples in the two unsafe variants; and conservatively
returns `unknown` on four safe regular-language problems that require DFA or
modulo-count invariant synthesis. The benchmark origins, known invariants, and
proposed L*/SAT-based automata-learning architecture are documented in
[`docs/string_invariant_literature.md`](docs/string_invariant_literature.md).


## Repository layout

```text
bounded_explorer.py       direct launcher
src/pyhorn_bnd/           parser, SeedMiner, MultiHoudini, VC/explorer, CLI
examples/                 syntax examples and extracted corpus cases
docs/                     implementation, Houdini, and parser specifications
tests/                    standalone and optional corpus regressions
tools/                    parser and seed-Houdini corpus utilities
```


## Version and compatibility

The package exposes its version through:

```python
import pyhorn_bnd
print(pyhorn_bnd.__version__)
```

Version `0.0.18` adds staged trace-guided candidate generation
(`--trace-houdini`): sampling concrete bounded reachable states and
generalizing them through a closed 15-template registry when syntactic
mining alone does not prove the program, plus a neutral
`CandidateGenerator`/`CandidateBatch` extension API that both `SeedMiner`
and the new `TraceCandidateMiner` implement, and an expanded
`StringSortProfile` that reports whether a program uses `str.len`. Version
`0.0.14` adds a literature-derived string-invariant benchmark suite,
parser/solver regressions, an audit tool, and a design specification for regular
invariant synthesis. Version `0.0.13` added native String/regular-expression parsing and
reasoning in both CHC syntaxes, including bounded exploration, Seed-Houdini, mixed length
arithmetic, string-valued arrays, Unicode escapes, and SMT dumps. Version
`0.0.12` makes real arithmetic an explicit tested contract across
parsing, SSA construction, both bounded solver modes, SeedMiner, MultiHoudini,
real-valued arrays, mixed `Int`/`Real` formulas, and SMT dumps. Version `0.0.11`
added complete original-suite parsing, benchmark-driven SeedMiner/Houdini
corner-case handling, and fresh final CHC certification. Version `0.0.10`
removed pre-1.0 compatibility aliases from the Python API
and CLI. Use `solver_mode="fresh"`, `smt_dump_dir=...`, `solver_backend`, and
`--dump-smt` directly.

The implementation contract is documented in
[`docs/implementation_spec.md`](docs/implementation_spec.md). Detailed Houdini
solver semantics are in
[`docs/houdini_incremental_solver_spec.md`](docs/houdini_incremental_solver_spec.md).


## Tests

```bash
python3 -m pip install pytest ruff
python3 -m pytest -q
python3 -m ruff check .
```

To run the complete external corpus regression:

```bash
PYHORN_BENCH_HORN_DIR=/path/to/bench_horn \
  python3 -m pytest -q tests/test_bench_horn_corpus.py
```

The ordinary test suite does not depend on the external corpus; it uses the ten
theory/operator cases in `examples/bench_horn/`, focused Seed-Houdini examples,
the real-arithmetic suite in `examples/real_arithmetic/`, the string-theory
suite in `examples/string_theory/`, and the original
benchmark edge cases in `examples/freqhorn_corner_cases/`.
