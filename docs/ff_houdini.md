# Combining forward-fixpoint and Houdini: `--ff-houdini`

`--ff` and Seed/Trace-Houdini fail for complementary reasons on some
inputs. `--ff-houdini` alternates between them, each round feeding what
one side found to the other, until one proves the program safe or
unsafe, neither makes further progress, or a round budget is exhausted.

```bash
pyhorn-expl --ff-houdini input.smt2
```

Cannot be combined with `--ff`, `--seed-houdini`, `--cands`,
`--phasefit`, or `--mut` -- it already runs its own seed-mining each
round on top of whatever forward-fixpoint contributes. Combine with
`--trace-houdini` to use Trace-Houdini's mining instead of plain
Seed-Houdini for the Houdini side of each round.

## Why they fail for different reasons

- `--ff`'s generalized (interval-widened) track can reach a genuine
  fixpoint that's still too loose to rule out a query -- a sound
  invariant, just not a tight enough one, because interval widening is
  non-relational and drops correlations between variables (see
  [`forward_fixpoint.md`](forward_fixpoint.md)).
- Seed-Houdini's syntactic mining is more thorough than it might look at
  first glance -- it doesn't just propose the negated query condition as
  a candidate, it also *weakens* every equality it finds anywhere in the
  program (a fact `x == 0` yields both `x >= 0` and `x <= 0` as
  candidates too), so it already covers most "the query needs a simple
  bound" cases unaided. What it has no mechanism for is a bound that
  only exists because of *forward reachability across a relation
  boundary* -- a value handed from one relation to another purely by
  argument position, with no literal comparison anywhere in the handoff
  rule for that weakening trick to find.

## The mechanism

Each round:

1. Run `--ff`. If it reaches SAFE or a confirmed UNSAFE, that verdict is
   final -- report it as-is (an `--ff-houdini` UNSAFE verdict is exactly
   `--ff`'s own independently-confirmed counterexample; see
   `forward_fixpoint.md`'s CAUTION note -- nothing new is derived here).
2. Otherwise, if `--ff`'s generalized track found its own fixpoint (even
   though not tight enough to prove safety alone), merge it into
   Houdini's candidate pool as one more candidate. This never needs any
   special protection against being incorrectly eliminated: Houdini only
   removes a candidate a genuine countermodel falsifies, and a
   generalized-track fixpoint is, by construction, unconditionally true
   for every real rule application -- no real countermodel can touch it.
3. Run Houdini (Seed- or Trace-, per `--trace-houdini`) with that
   merged pool. Success is final.
4. Otherwise, check whether Houdini's own elimination loop stabilized
   before it ever got to certifying queries -- `MultiHoudini`'s
   elimination runs to its own internal fixed point, checking every fact
   and step rule (not query rules), strictly before the separate final
   certification step that additionally checks queries. So when every
   remaining certification failure is on a query rule specifically, the
   retained candidates are already a proven invariant regardless of the
   overall verdict -- just not tight enough to rule the query out yet.
   Feed that back into the next round's `--ff` run as an external fact:
   it tightens (or, for a tainted relation, entirely replaces) whatever
   `--ff` would otherwise have to derive from raw ENTRY facts on its
   own. If any non-query rule also failed certification -- ordinarily a
   sign of a solver `unknown` rather than an actual gap, since the
   elimination loop's own checks already covered those same rules --
   alternation stops rather than risk feeding back something that was
   never actually confirmed closed.
5. Repeat, up to `--ff-houdini-max-rounds` (default 3) or until a round
   produces nothing new.

## A verified example

This program hands a value from relation `a` to relation `b` purely by
argument position -- `(rule (=> (a c len) (b c 0 0)))` has no literal
comparison on `c`/`x` at all -- then uses that value's sign to select
between two `ite` branches in `b`'s own step rule. Proving the safety
property (`y == 2*steps`) requires knowing `x >= 0`, which is true (`a`'s
own value only ever increases from 0) but isn't recoverable by weakening
any literal in the program:

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

$ pyhorn-expl --ff-houdini gap.smt2
Success
```

`--ff` alone finds `x >= 0` (via widening `a`'s own value, propagated
through the handoff) but can't establish `y == 2*steps` on its own
(non-relational). `--seed-houdini` alone finds `y == 2*steps` (directly
from the negated query) but can't establish `x >= 0` for `b`, since
nothing in the handoff rule gives its weakening trick anything to grab
onto. Together, one round is enough.

## CLI reference

| Flag | Default | Meaning |
| --- | --- | --- |
| `--ff-houdini` | off | Enable the alternation. |
| `--ff-houdini-max-rounds` | 3 | Round budget before giving up with UNKNOWN. Requires `--ff-houdini`. |
| `--trace-houdini` | off | Use Trace-Houdini instead of Seed-Houdini for the Houdini side of each round. |
| `--ff-max-iterations`, `--ff-timeout-ms`, `--ff-overall-timeout-s`, `--ff-no-generalization`, `--ff-widening-delay` | see `forward_fixpoint.md` | Apply to the forward-fixpoint side of each round. Also require `--ff-houdini` (or plain `--ff`). |
| `--to`, `--random-seed` | see main `--help` | Apply to the Houdini side of each round, same as every other Houdini-based mode. |

### Exit codes, output, and JSON fields

Same convention as `--ff`: `0` SAFE (prints `Success`), `1` UNSAFE
(prints `counterexample` plus a model), `2` UNKNOWN (prints `unknown`),
`3` parse failure. `--print-invariants` prints each relation's retained
invariant conjuncts on SAFE. `--json` prints `status`, `rounds`,
`message`, `violated_rule`, and `counterexample` -- no
`qe_unsound_rejections` field here, since any UNSAFE verdict is `--ff`'s
own already fully independently-confirmed one (see `forward_fixpoint.md`).
