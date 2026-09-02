# Alternating Houdini and forward-fixpoint: `--ff-houdini`

`--ff-houdini` alternates real Houdini elimination and an
invariant-accelerated forward-fixpoint pass in rounds, each feeding the
other, up to a round budget:

```bash
pyhorn-expl --ff-houdini input.smt2

# broadened with every other candidate source at once
pyhorn-expl --ff-houdini --cands extra.smt2 --phasefit --trace-houdini --mut input.smt2
```

This is a substantially different technique from an earlier version of
this flag, which seeded forward-fixpoint individually from one candidate
at a time (no Houdini elimination at all). That mechanism -- it was
never really "Houdini" in the sense of running `MultiHoudini`'s
elimination, only reusing its candidate-generating techniques -- now
lives under `--ff-seeded`, generalized to draw from the same sources;
see [`forward_fixpoint.md`](forward_fixpoint.md)'s `--ff-seeded` section.

## The mechanism

Each round:

1. **Houdini, on all candidates at once.** Run `MultiHoudini` on the full
   candidate pool: SeedMiner's own full syntactic mining (fact-, step-,
   and query-rule provenance alike, *always* -- this differs from
   `--ff-seeded`'s narrower fact-rule-only default; see below for why),
   plus whichever of `--cands`, `--phasefit`, `--mut`, and
   `--trace-houdini` were also requested. If that alone certifies every
   rule -- including the query rules -- Houdini has already proven the
   program SAFE outright: done, no forward-fixpoint pass needed.
2. **Feed the proven invariants into an accelerated forward-fixpoint
   pass.** If certification instead leaves only *query*-rule failures
   (a query failure just means the invariants found aren't *sufficient*
   yet to rule the query out -- it doesn't mean anything is unsound), the
   surviving candidates become `external_invariants` for one
   `run_forward_fixpoint` pass: propagating some `P` through a
   transition relation `TR` now computes the strongest `Q` such that
   `P /\ TR /\ Invs => Q` instead of just `P /\ TR => Q`, and `P \/ Q`
   feeds the next iteration as usual (see
   [`forward_fixpoint.md`](forward_fixpoint.md)'s `external_invariants`
   field). A genuine *non-query* certification failure, on the other
   hand, means nothing this round can be trusted as a real invariant, so
   nothing is fed forward that round -- the pass still runs, just
   unaccelerated (matching plain `--ff`). SAFE or a confirmed UNSAFE from
   this pass stops everything immediately.
3. **Otherwise, alternate again.** The accelerated pass's own
   per-relation reachable-set formulas -- genuinely computed facts about
   the program, not syntactic guesses -- are added as new candidates for
   the *next* round's Houdini pass, together with the *entire original*
   candidate pool again, including whatever this round's Houdini pass
   eliminated: a candidate that didn't survive alone might still combine
   usefully with a newly-computed reachable-set formula. A reachable-set
   formula that's grown too large to be a useful Houdini candidate in the
   first place (measured during development: a genuine ~750,000-character
   formula after several non-converging iterations) is dropped rather
   than fed forward. Repeats up to `--ff-houdini-max-rounds` (default 3),
   stopping early with UNKNOWN the moment a round's candidate pool is
   identical to the previous round's -- both sides are deterministic, so
   a repeated pool can only repeat the same outcome.

## Why the default candidate pool is broader than `--ff-seeded`'s

`--ff-seeded` needs each candidate to be a sound `initial_seed` *by
construction*, with no independent check beyond initiation -- that's
why its own default is restricted to fact-rule-provenance conjuncts.
A real Houdini pass is different: it independently verifies
inductiveness of *any* candidate itself, via fresh certification against
every rule, regardless of where the candidate came from. There's no
reason to withhold step- or query-rule-derived candidates the way
`--ff-seeded` must -- and in practice they're often exactly what's
needed (a relational fact like `y == 2*x`, mined straight from a negated
query, is the routine case). So `--ff-houdini` always uses SeedMiner's
full mining as its base, and `--seed-houdini` has no separate,
CLI-visible effect here (this is the one difference from `--ff-seeded`,
where `--seed-houdini` is a genuine toggle).

## A verified example

This program's safety depends on an array-equality invariant (`a == b`)
that a store at index 1 appears to break, but the mined atom
`(select a 0) == 0` still transfers correctly under the substitution
`a == b`. Houdini's first pass, on the plain syntactically-mined
candidates alone, can't quite certify this; feeding its own accelerated
forward-fixpoint pass's result back in for a second Houdini pass does:

```smt2
(declare-var a (Array Int Int))
(declare-var b (Array Int Int))
(declare-var i Int)
(declare-var v Int)
(declare-rel inv ((Array Int Int) (Array Int Int) Int))
(declare-rel done (Int))
(declare-rel fail ())

(rule (inv ((as const (Array Int Int)) 0)
           ((as const (Array Int Int)) 0)
           0))
(rule
  (=> (and (inv a b i) (= a b) (= (select a 0) 0))
      (inv (store a 1 5) (store b 1 7) i)))
(rule
  (=> (and (inv a b i) (not (= a b)))
      (inv (store a 1 5) (store b 1 7) i)))
(rule
  (=> (inv a b i)
      (done (select b 0))))
(rule
  (=> (and (done v) (not (= v 0)))
      fail))
(query fail)
```

```bash
$ pyhorn-expl --ff array_eq.smt2
unknown

$ pyhorn-expl --seed-houdini array_eq.smt2
unknown

$ pyhorn-expl --ff-houdini --debug array_eq.smt2
2 round(s): round 2: Houdini certified 11 candidate(s) as inductive, ruling out every query directly
Success
```

Neither plain `--ff` (no candidates at all, just literal fact-rule
seeding) nor plain `--seed-houdini` (candidates checked, but never
combined with any actual forward propagation) proves this alone. The
alternation does, specifically because round 1's Houdini pass isn't
enough by itself, but round 2's -- fed by round 1's accelerated
forward-fixpoint pass -- is.

## CLI reference

| Flag | Default | Meaning |
| --- | --- | --- |
| `--ff-houdini` | off | Enable the technique. |
| `--ff-houdini-max-rounds` | 3 | Round budget for the alternation. Requires `--ff-houdini`. |
| `--cands FILE` | -- | Merge user-supplied candidates into the pool. |
| `--phasefit` | off | Merge PhaseFit's interval lemmas into the pool. |
| `--trace-houdini` | off | Merge trace-sampled generalizations into the pool. |
| `--mut` | off | Apply pairwise mutation over the complete combined pool. |
| `--seed-houdini` | -- | Accepted but has no separate effect here -- SeedMiner's full mining is always included (see above). |
| `--ff-max-iterations`, `--ff-timeout-ms`, `--ff-overall-timeout-s`, `--ff-no-generalization`, `--ff-widening-delay` | see `forward_fixpoint.md` | Apply to every accelerated (or unaccelerated) forward-fixpoint attempt this makes. |
| `--to` | see main `--help` | Applies to both Houdini's own per-check timeout and trace mining. |
| `--random-seed` | see main `--help` | Applies to both Houdini and trace mining. |

Cannot be combined with plain `--ff` or `--ff-seeded` -- each is a
different, standalone technique for using forward-fixpoint.

### Exit codes, output, and JSON fields

Same convention as `--ff`: `0` SAFE (prints `Success`), `1` UNSAFE
(prints `counterexample` plus a model), `2` UNKNOWN (prints `unknown`),
`3` parse failure (of either the program file or a `--cands` file).
`--print-invariants` prints each relation's proven invariant formula on
SAFE -- Houdini's own certified conjunction if that's what settled it,
or forward-fixpoint's own reachable-set formula otherwise. `--debug`
additionally prints the round count and a one-line summary of what
happened. `--json` prints `status`, `message`, `rounds`,
`violated_rule`, and `counterexample`.
