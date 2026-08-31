# Forward-fixpoint seeded from a flexible candidate pool: `--ff-houdini`

`--ff-houdini` generalizes `--ff-seeded`'s "try one sound fact-rule
conjunct at a time as `initial_seed`" strategy (see
[`forward_fixpoint.md`](forward_fixpoint.md)'s `--ff-seeded` section) from
a single, fixed candidate source to *any* combination of this codebase's
candidate-generating techniques. By default (nothing else given) it
draws only from SeedMiner's own mining (the same mining `--seed-houdini`
uses); passing `--cands`, `--phasefit`, `--mut`, and/or `--trace-houdini`
alongside it broadens the pool with those techniques' own candidates.

```bash
pyhorn-expl --ff-houdini input.smt2

# broadened with every other candidate source at once
pyhorn-expl --ff-houdini --cands extra.smt2 --phasefit --trace-houdini --mut input.smt2
```

Unlike an earlier version of this flag, `--ff-houdini` is now compatible
with every one of `--seed-houdini`, `--cands`, `--phasefit`, `--mut`,
`--trace-houdini`, and `--ff-seeded` -- the only thing it still cannot be
combined with is plain `--ff`, since it is itself a different,
standalone way of using forward-fixpoint. `--ff-seeded` specifically has
no separate effect alongside it: `--ff-seeded`'s own fact-rule-conjunct
strategy is exactly `--ff-houdini`'s default candidate source.

`--seed-houdini` is only ever a genuine toggle once `--cands` and/or
`--trace-houdini` is also given -- exactly like it is for the ordinary
Houdini CLI pipeline. With neither of those given, SeedMiner's mining
runs regardless (that's the default pool above), so bare
`--ff-houdini --seed-houdini` is a no-op. But `--cands`/`--trace-houdini`
build a pool from just what was actually asked for -- *not* the default
SeedMiner pool too -- so `--ff-houdini --trace-houdini` alone and
`--ff-houdini --trace-houdini --seed-houdini` genuinely differ:

```bash
$ pyhorn-expl --ff-houdini --trace-houdini --debug gap.smt2
gathered 20 candidate(s), 16 initiation-sound; ...

$ pyhorn-expl --ff-houdini --trace-houdini --seed-houdini --debug gap.smt2
gathered 33 candidate(s), 28 initiation-sound; ...
```

`--phasefit` is the one exception to this: it needs a mined
`SeedMiningResult` of its own for atom harvesting regardless of
`--seed-houdini`, so its candidates end up in the pool either way --
matching the ordinary Houdini CLI pipeline's own documented reasoning
for the same situation (relations PhaseFit doesn't touch, or fails to
split, would otherwise get no candidates at all from a `--phasefit`-only
run).

## The mechanism

1. **Gather.** Build a candidate pool: SeedMiner's full mining
   (fact-, step-, and query-rule provenance alike) forms the base by
   default, and remains included regardless once `--seed-houdini` is
   given explicitly; `--cands`, `--phasefit`, and `--trace-houdini` each
   merge their own candidates in when requested (see above for exactly
   when SeedMiner's own mining is, and isn't, included alongside them);
   `--mut` is applied last, over the complete combined pool, deriving
   pairwise-combined candidates from it.
2. **Filter by initiation.** Every candidate gathered this way is just a
   formula over its relation's canonical variables -- nothing guarantees
   it actually holds at that relation's own entry point. A step- or
   query-rule-derived atom, a PhaseFit lemma, a trace-sampled
   generalization, or a user's own guess can just as easily describe a
   *later* reachable state as an initial one. Each candidate is checked
   against **initiation** -- `Init(relation) => candidate`, where
   `Init(relation)` is that relation's own literal fact-rule condition --
   and dropped if it fails. This is exactly the soundness condition
   `ForwardFixpoint.run` itself enforces (raising `ValueError` if
   violated) for any `initial_seed`; checking it here upfront lets a
   whole pool of untrusted candidates be filtered down to the sound ones
   instead of finding out one at a time via that exception. Fact-rule
   conjuncts (the default source) pass this trivially, by construction,
   exactly as they do for `--ff-seeded`.
3. **Propagate individually.** Each surviving candidate is tried on its
   own, in turn, exactly the way `--ff-seeded` tries each fact-rule
   conjunct: it becomes the `initial_seed` override for *its* relation
   only, while every other relation keeps its own normal, full fact-rule
   seeding. The first SAFE or confirmed UNSAFE stops the search
   immediately.
4. **No further fallback.** If nothing in the pool settles the question,
   the result is UNKNOWN. There is no additional attempt that seeds every
   relation from its full, literal fact-rule condition at once (a "whole
   formula" propagation), and no `MultiHoudini`-style elimination pass
   over the pool as a single unit either -- an earlier version of this
   module alternated full `--ff` runs with full Houdini runs across
   several rounds; this version does neither. Per
   [`forward_fixpoint.md`](forward_fixpoint.md)'s own measurement, a
   smaller, single-fact seed is not just cheaper than a joint computation
   over every variable at once -- it can outright prove things the joint
   computation cannot, since variables a query genuinely doesn't depend
   on can make quantifier elimination *less* able to find a proof, not
   just slower. Trying every sound candidate individually is this
   module's only mechanism.

## Why this reaches cases neither underlying technique proves alone

Plain `--ff` always seeds every relation from its full, literal
fact-rule condition -- the "whole formula" this module deliberately
avoids. Plain `--seed-houdini` never propagates anything forward at all;
it only mines candidates syntactically and filters them with
`MultiHoudini`. `--ff-houdini` combines what each contributes -- the
candidate-generating machinery of Seed-/Trace-/PhaseFit-Houdini feeding
individual, genuine forward reachability computation -- without ever
paying for (or being limited by) either one's own "everything at once"
approach.

## A verified example

This program hands a value from relation `a` to relation `b` purely by
argument position -- `(rule (=> (a c len) (b c 0 0)))` has no literal
comparison on `c`/`x` at all -- then uses that value's sign to select
between two `ite` branches in `b`'s own step rule. Proving the safety
property (`y == 2*steps`) requires knowing `x >= 0`, which is true (`a`'s
own value only ever increases from 0) but isn't recoverable by weakening
any literal in the program, and plain `--ff`'s exact, literal seeding of
`a` (`c == 0`) doesn't converge to a usable proof either:

```smt2
(set-logic HORN)
(declare-var c Int)
(declare-var c1 Int)
(declare-var len Int)
(declare-var x Int)
(declare-var y Int)
(declare-var steps Int)
(declare-var y1 Int)
(declare-var steps1 Int)
(declare-rel a (Int Int))
(declare-rel b (Int Int Int))
(declare-rel fail ())

(rule (a 0 len))
(rule (=> (and (a c len) (< c len) (= c1 (+ c 1))) (a c1 len)))
(rule (=> (a c len) (b c 0 0)))
(rule (=> (and (b x y steps) (< steps 5)
               (= y1 (+ y (ite (>= x 0) 2 (- 2))))
               (= steps1 (+ steps 1)))
          (b x y1 steps1)))
(rule (=> (and (b x y steps) (not (= y (* 2 steps)))) fail))
(query fail)
```

```bash
$ pyhorn-expl --ff gap.smt2
unknown

$ pyhorn-expl --seed-houdini gap.smt2
unknown

$ pyhorn-expl --ff-houdini --debug gap.smt2
gathered 16 candidate(s), 15 initiation-sound; tried 1 before succeeding with a: 0 <= __a_0
Success
```

`--ff` alone, seeded from `a`'s exact fact-rule condition, cannot
establish `y == 2*steps` (non-relational widening). `--seed-houdini`
alone finds `y == 2*steps` (directly from the negated query) but has no
literal in the handoff rule to weaken into `x >= 0` for `b`. Seeding
forward-fixpoint from the weakened fact-rule atom `0 <= __a_0` mined for
`a` -- one of SeedMiner's own default candidates -- is enough on its own:
its closure under the step rules is looser than the exact fact-rule
seeding but converges to a genuine fixpoint that already rules the query
out.

## CLI reference

| Flag | Default | Meaning |
| --- | --- | --- |
| `--ff-houdini` | off | Enable the technique. |
| `--cands FILE` | -- | Merge user-supplied candidates into the pool. |
| `--phasefit` | off | Merge PhaseFit's interval lemmas into the pool. |
| `--trace-houdini` | off | Merge trace-sampled generalizations into the pool. |
| `--mut` | off | Apply pairwise mutation over the complete combined pool. |
| `--seed-houdini` | -- | A genuine toggle once `--cands` and/or `--trace-houdini` is also given; a no-op alongside bare `--ff-houdini` or `--phasefit` (see above). |
| `--ff-seeded` | -- | Accepted alongside `--ff-houdini` but has no separate effect there (see above). |
| `--ff-max-iterations`, `--ff-timeout-ms`, `--ff-overall-timeout-s`, `--ff-no-generalization`, `--ff-widening-delay` | see `forward_fixpoint.md` | Apply to every individual forward-fixpoint attempt this makes. Also require `--ff-houdini` (or plain `--ff`/`--ff-seeded`). |
| `--trace-depth`, `--trace-limit`, `--trace-models-per-prefix`, `--trace-samples-per-predicate`, `--trace-candidates-per-predicate` | see main `--help` | Apply to trace mining when `--trace-houdini` is also given. |
| `--to`, `--random-seed` | see main `--help` | `--random-seed` applies to trace mining, when used. |

`--ff-houdini-max-rounds` no longer exists: there is no alternation or
round budget left to bound (see "The mechanism" above).

### Exit codes, output, and JSON fields

Same convention as `--ff`: `0` SAFE (prints `Success`), `1` UNSAFE
(prints `counterexample` plus a model), `2` UNKNOWN (prints `unknown`),
`3` parse failure (of either the program file or a `--cands` file).
`--print-invariants` prints each relation's reachable-set formula on
SAFE, the same way `--ff`/`--ff-seeded` do. `--debug` additionally prints
how many candidates were gathered, how many passed the initiation
filter, how many were actually tried, and which relation/candidate (if
any) settled the question. `--json` prints `status`, `message`,
`candidates_gathered`, `candidates_sound`, `attempts`,
`winning_relation`, `winning_candidate`, `violated_rule`, and
`counterexample` -- no `rounds` field (there is no alternation to count
rounds of) and no `qe_unsound_rejections` field (any UNSAFE verdict is
the winning forward-fixpoint run's own already fully independently-
confirmed one -- see `forward_fixpoint.md`).
