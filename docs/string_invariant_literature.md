# String invariant synthesis: literature benchmarks and solver roadmap

**PyHorn version:** 0.0.14  
**Benchmark directory:** `examples/string_invariant_literature/`

## 1. Purpose

This suite turns representative string-verification problems from the literature
into linear CHCs accepted by PyHorn. It has three goals:

1. exercise parsing and normalization of nontrivial string constraints;
2. distinguish problems already handled by SeedMiner + MultiHoudini from
   problems requiring regular-language synthesis;
3. provide a concrete roadmap for a future string-invariant backend.

The suite intentionally includes safe and unsafe systems. An unsafe system is
useful because bounded exploration should find a concrete derivation, while a
safe system tests whether the candidate language is expressive enough to prove
all CHCs.

## 2. Literature basis

The primary source is HornStr, which formulates regular model checking as CHCs
over SMT-LIB strings and synthesizes regular invariants using either Angluin-style
L* automata learning or SAT-based DFA learning:

- H. Jiang, A. W. Lin, O. Markgraf, P. Rümmer, D. Stan,
  *HornStr: Invariant Synthesis for Regular Model Checking as Constrained Horn
  Clauses*, CAV 2025 / arXiv:2505.15959.
- Artifact: <https://doi.org/10.5281/zenodo.15153023>.

The token-passing and MU-puzzle CHCs are manually re-encoded from Examples 1
and 2 of that paper. The coffee-can and single-token examples are standard
regular-model-checking patterns. The sanitizer and character-copy examples are
small program-analysis models inspired by the string-constraint-verification
literature.

Relevant background includes:

- D. Angluin, *Learning Regular Sets from Queries and Counterexamples*, 1987.
- A. Bouajjani et al., regular model checking and automata-based verification of
  parameterized systems.
- R. Amadini, G. Gange, P. Stuckey, *A Survey on String Constraint Solving*,
  ACM Computing Surveys 2021.

## 3. Benchmark inventory

| Benchmark | CHC shape | Expected result | Useful invariant | Current result |
|---|---|---|---|---|
| `hornstr_token_pass_safe.smt2` | regex initial set; three word-equation transitions; regex bad set | safe | `n* r n (nn)* b n*` | Seed-Houdini: `unknown` |
| `hornstr_mu_puzzle_safe.smt2` | singleton initial state; four rewrite rules | safe | starts with `M`; number of `I` symbols is not `0 mod 3` | Seed-Houdini: `unknown` |
| `hornstr_mu_puzzle_unsafe_miu.smt2` | MU rewriting with reachable target `MIU` | unsafe | not applicable | bounded CEX at depth 3 |
| `coffee_can_odd_white_safe.smt2` | four local string-rewrite rules | safe | odd number of `W` symbols | Seed-Houdini: `unknown` |
| `single_token_line_safe.smt2` | one local move rule; regex bad set | safe | `N* T N*` | Seed-Houdini: `unknown` |
| `regex_alphabet_closure_safe.smt2` | append-only transition; regex complement query | safe | `(a|b)*` | Seed-Houdini: `unknown` (Z3 regex-complement certification timeout, not a mining gap -- see below) |
| `html_escape_stream_safe.smt2` | two-string state; `str.at`, `substr`, concatenation, containment | safe | output contains neither `<` nor `>` | Seed-Houdini: `Success` |
| `html_escape_stream_unsafe.smt2` | buggy sanitizer | unsafe | not applicable | bounded CEX at depth 3 |
| `copy_decomposition_safe.smt2` | three-string state; character transfer | safe | `original = output ++ remaining` | Seed-Houdini: `Success` |
| `replace_sanitize_safe.smt2` | restricted alphabet / no raw `<` | safe | `not (str.contains s "<")` | Seed-Houdini: `Success` |
| `prefix_closure_safe.smt2` | prefix-closed fragment of `aaa` | safe | `str.prefixof s "aaa"` | Seed-Houdini: `Success` |
| `short_word_unsafe.smt2` | single rewrite to bad word `ab` | unsafe | reachable at depth 3 | bounded exploration |

The current results are regression expectations, not completeness claims. A
safe benchmark returning `unknown` means the mined candidate set or Z3 backend
was insufficient; it does not mean the benchmark is unsafe.

## 4. CHC encodings

### 4.1 Regular model checking

A configuration word is represented by one SMT-LIB `String`. A transition is a
word equation describing replacement of a local substring:

```smt2
(assert
  (forall ((vi String) (vo String) (x String) (y String))
    (=> (and (inv vi)
             (= vi (str.++ x "TN" y))
             (= vo (str.++ x "NT" y)))
        (inv vo))))
```

Regular initial or bad sets use `str.in_re`:

```smt2
(str.in_re vi
  (re.++ (re.* (str.to_re "N"))
         (str.to_re "T")
         (re.* (str.to_re "N"))))
```

This is a linear CHC: there is one source predicate occurrence and one
destination predicate occurrence.

### 4.2 String rewriting

The MU and coffee-can systems use existentially chosen contexts represented by
universally quantified rule variables. For example:

```smt2
(= vi (str.++ x "III" y))
(= vo (str.++ x "U" y))
```

The CHC quantification means that any decomposition satisfying the equation may
be used for a transition.

### 4.3 String programs

The sanitizer and copy examples encode loop state as multiple predicate
arguments. They combine strings with integer length constraints:

```smt2
(inv remaining output)
(> (str.len remaining) 0)
(str.substr remaining 1 (- (str.len remaining) 1))
(str.at remaining 0)
```

The copy example requires a relational word equation across three state
components. This is not merely a unary regular-language invariant.

## 5. Parser and regression contract

Every benchmark must satisfy all of the following:

1. `parse_chc_file(..., slice_program=False)` succeeds.
2. The normalized program contains at least one rule and exactly one query
   relation.
3. Every source and destination argument has the declared relation sort.
4. `HornProgram.string_sorts.uses_string` is true.
5. The two HornStr examples preserve both word-equation operations and regular
   constraints where present.
6. Unsafe examples are found in both bounded solver modes at their expected
   minimal depth.
7. Easy safe examples are freshly certified after MultiHoudini.
8. Hard regular examples remain conservative `unknown` until a regular-language
   learner is implemented.

Run the focused suite with:

```bash
python3 -m pytest -q tests/test_string_invariant_literature.py
```

Run a machine-readable audit with:

```bash
PYTHONPATH=src python3 tools/audit_string_invariant_benchmarks.py \
  --timeout 2000 \
  --bounded-depth 6 \
  --json
```

## 6. Why the current SeedMiner solves only part of the suite

SeedMiner observes Boolean subtrees already present in the CHCs, projects them
onto canonical predicate variables, and lets MultiHoudini remove non-inductive
candidates. This works when a useful invariant appears syntactically in a fact,
transition, or query, for example:

- `(not (str.contains output "<"))`;
- `(not (str.contains output ">"))`;
- `original = output ++ remaining`;
- membership in `(a|b)*` obtained by negating the regex-complement query.

The hard RMC cases need invariants that are not direct subformulas:

- parity or modulo counting of characters;
- a newly discovered DFA with several states;
- a regular language strictly between the reachable set and the bad set;
- closure under multiple rewrite relations.

Houdini can filter a finite candidate set, but it cannot invent those automata.

## 7. Proposed regular-invariant synthesis backend

### 7.1 Candidate representation

For each unary string predicate `P`, represent a candidate invariant by a DFA:

```text
DFA_P = (alphabet, states, initial_state, transition, accepting_states)
```

Compile the DFA to an SMT regular expression only when asking the string solver
for a proof obligation. Keep the automaton as the primary representation to
avoid exponential regex expansion.

For predicates with additional finite-domain or arithmetic state, use a product
of:

- a DFA over the string component;
- a finite abstraction of auxiliary components;
- optional Houdini candidates for relational constraints.

### 7.2 Alphabet extraction

Build a finite abstract alphabet from:

- characters occurring in string literals;
- singleton/range regexes;
- a distinguished `OTHER` class for all remaining Unicode characters.

For the current RMC benchmarks, the literal alphabet is sufficient (`M`, `I`,
`U`; `B`, `W`; `N`, `T`; `n`, `r`, `b`). The `OTHER` class is necessary for
soundness on general SMT-LIB strings.

### 7.3 Teacher queries

An automata learner needs two kinds of query.

#### Membership query

Ask whether a concrete word belongs to the least reachable interpretation of a
predicate. Exact reachability is undecidable in general, so the teacher may be:

- bounded reachability plus memoization;
- backward reachability for local rewrite systems;
- a strict/inductive teacher that can answer with additional counterexamples;
- an SMT encoding of a finite derivation.

A conservative `unknown` answer must not be treated as membership or
non-membership.

#### Equivalence / inductiveness query

Given DFA invariants, check all CHCs:

- initiation: `Init ∧ ¬I`;
- consecution: `I_src ∧ Transition ∧ ¬I_dst`;
- safety: `I ∧ Bad`.

A SAT model supplies a counterexample word or word pair. It is classified as:

- **positive**: reachable but rejected by the candidate;
- **negative**: accepted by the candidate and reaches the bad set;
- **implication counterexample**: source accepted, transition enabled, output
  rejected.

The learner refines from these counterexamples.

### 7.4 Learning algorithms

Two practical options mirror the literature.

#### L* learning

Use an observation table with membership and equivalence queries. L* is a good
fit when membership answers are available and the target invariant has a small
minimal DFA.

For CHCs, implication counterexamples require an inductive or strict teacher;
the learner is not simply learning the exact reachable language.

#### SAT-based DFA synthesis

For a fixed state bound `n`, introduce Boolean variables for DFA transitions
and accepting states. Encode:

- all positive/negative sample classifications;
- all implication counterexamples;
- optional symmetry breaking and totality.

Increase `n` until a candidate passes all CHC checks. This avoids membership
queries but may produce large SAT instances.

### 7.5 Solver backend boundary

Z3 is useful for word equations, concrete membership constraints, and many
mixed string/arithmetic checks. Its string/regex support is incomplete, and the
hard equivalence obligations in the MU, coffee-can, and token-passing examples
can return `unknown` or time out.

The regular learner should therefore use a backend interface:

```python
class StringImplicationBackend(Protocol):
    def check_initiation(...): ...
    def check_consecution(...): ...
    def check_safety(...): ...
```

Possible implementations:

1. Z3-only, with conservative `unknown`;
2. an external string solver such as Z3-Noodler or OSTRICH;
3. direct automata/transducer operations for the regular fragment;
4. a portfolio that tries direct automata reasoning before SMT.

The invariant must be independently certified before `Success` is reported.

## 8. Benchmark-specific solution ideas

### 8.1 HornStr token passing

Known regular invariant:

```text
n* r n (nn)* b n*
```

The most direct solution is DFA learning from initiation, the three local
rewrite relations, and the bad regex. Direct automata image/preimage operations
are preferable because every transition is a rational/local rewrite relation.

### 8.2 MU puzzle

The classic proof uses the number of `I` symbols modulo 3. Starting from `MI`,
the reachable residue is never 0, while `MU` has residue 0.

Two encodings are useful:

- a three-state counting DFA over `{M,I,U}`;
- a Parikh abstraction with an integer ghost `i_mod_3`.

The DFA route stays entirely within regular invariants. A future candidate
factory can synthesize character-count modulo automata directly before invoking
a general learner.

### 8.3 Coffee-can rewriting

The parity of `W` is invariant. The initial word `WWWB` has odd parity, while
`B` has even parity. A two-state parity DFA is sufficient.

This is another strong case for a specialized modulo-count candidate factory.

### 8.4 Single-token line

Invariant:

```text
N* T N*
```

A small DFA can be synthesized from the initial word, the `TN -> NT`
transition, and the two-token bad language. Because the benchmark has a fixed
initial length but the invariant is length-independent, learning should prefer
a small automaton over enumerating reachable words.

### 8.5 Sanitizer and copy loops

These are better served by the existing SeedMiner/Houdini architecture:

- sanitizer: unary containment predicates;
- copy: a relational word equation over multiple state components.

A pure DFA learner cannot express the copy invariant without encoding tuples or
using a multi-tape automaton. PyHorn should keep Houdini as a complementary
relational candidate engine.

## 9. Recommended implementation phases

### Phase 1: checked-in benchmark foundation

- Keep this twelve-file suite and manifest.
- Run parser/typechecking tests on every commit.
- Record bounded and Seed-Houdini outcomes without overclaiming hard cases.

### Phase 2: specialized regular candidates

- Character-count modulo DFAs.
- Exactly-one-symbol and at-most-one-symbol DFAs.
- Alphabet closure and prefix/suffix pattern DFAs.
- Convert generated DFAs to candidate predicates accepted by MultiHoudini.

This phase should solve MU, coffee-can, and single-token examples cheaply.

### Phase 3: general DFA learner

- Implement SAT-based bounded-state DFA synthesis first because it does not
  require a complete membership teacher.
- Add counterexample-guided CHC checking.
- Add L* once a robust membership/strict-teacher interface exists.

### Phase 4: backend portfolio and certification

- Add direct automata checks for regular transition fragments.
- Add optional external string-solver adapters.
- Certify every learned invariant with an independent backend or direct automata
  inclusion check.
- Return `unknown` on any unresolved proof obligation.

## 10. Soundness requirements

1. A learned candidate is never accepted solely because the learner converged.
2. Every original CHC must be certified under the final candidate set.
3. Any SMT or automata backend `unknown` propagates to PyHorn `unknown`.
4. Finite alphabet abstraction must include a sound `OTHER` class.
5. Bounded reachability may refute safety but may not prove unbounded safety.
6. Specialized modulo abstractions must be compiled to a concrete DFA or a
   separately certified arithmetic invariant.
7. String literals and regex ranges use SMT-LIB Unicode semantics, not bytes.

## 11. Current audit result

With Z3 4.16.0, a 2-second per-check timeout, and bounded depth 6:

```text
12 benchmarks parsed
5 safe benchmarks certified by Seed-Houdini
3 unsafe benchmarks refuted by bounded exploration at depth 3
4 safe regular-invariant benchmarks conservatively reported unknown
0 parser or internal errors
```

This is the intended baseline for version 0.0.14.

### 11.1 Update: a fifth hard case, of a different kind

`regex_alphabet_closure_safe.smt2` was originally counted among the safe
benchmarks Seed-Houdini certifies, not among the four `unknown` ones above.
That no longer holds under the Z3 versions available at the time of this
update (confirmed on both 5.0.0 and 4.16.0.0): SeedMiner finds the exact
correct candidate every time, but the final certification check --
`s in (a|b)*  and  s in Complement((a|b)*)`, about as simple as a
regex-emptiness check gets -- times out regardless. This is a different
failure mode from the four cases above, which fail because SeedMiner
cannot synthesize the needed invariant at all; here it does, and the
solver still can't close the check. See
`tests/test_string_invariant_literature.py`'s
`test_regex_complement_is_accepted_but_certification_is_a_known_hard_case`
and `diagnose_regex_minimal.py` at the repo root for the isolated repro.
