# Forward fixpoint: direct reachability via quantifier elimination

`--ff` is a third, independent analysis strategy alongside Seed-Houdini
(guess syntactic candidates, validate by SMT induction checks) and PhaseFit
(guess candidates from per-branch closed-form analysis). It doesn't guess at
all: it directly computes each relation's set of reachable states by
symbolic forward image iteration, using Z3's QE (quantifier elimination)
tactic to eliminate the existentially quantified predecessor state at each
step.

```bash
pyhorn-expl --ff --print-invariants input.smt2
```

Unlike Seed-Houdini and PhaseFit, this can prove **UNSAFE** with a genuine
counterexample, not just SAFE. It cannot be combined with `--seed-houdini`,
`--cands`, `--trace-houdini`, `--phasefit`, or `--mut` -- it's a standalone,
self-contained technique with its own iteration loop.

## Algorithm

Each round, for every non-fact, non-query rule, the current formula for
`rule.dst_relation` is set to the union of what it already contained and
this round's *image*: the rule body, instantiated with the current
reachable-set formula for `rule.src_relation` as a hypothesis, with the
rule-local variables existentially eliminated via Z3's `qe` tactic. This
repeats until one of three things happens:

- **The image stops growing for every relation.** Each relation's formula
  is then, by construction, exactly its set of reachable states -- an
  inductive invariant, since nothing new is ever reachable from it. If no
  query rule is satisfiable under it, the program is **SAFE**, and provably
  so: the literal reachable-state set, not a guess that survived
  validation.
- **A query rule's bad condition becomes satisfiable** under the current
  (already fully sound, since every image step is an exact forward step)
  reachable-set formula. The program is **UNSAFE**, with a genuine
  counterexample, not a possible one.
- **Neither happens within the iteration budget.** **UNKNOWN.**

That third case is the common one for genuinely unbounded loops (a plain
counter with no upper bound, say): the exact reachable set keeps growing
forever, and a naive iteration has no way to jump ahead to it.

## A caution about the exact track's own soundness

The "UNSAFE means a genuine counterexample" claim above rests on an
assumption that has been observed to be false in practice: that Z3's
`qe` tactic, when it returns a leak-free result, has computed something
genuinely equivalent to the existential it was asked to eliminate.

On a real benchmark combining integer `%` (mod) with `If`/ite in the
same rule body, `qe` returned a formula satisfied by a state with no
real predecessor under the actual rule -- confirmed by a direct,
tactic-free SAT check, and reproduced even with a 60-second timeout, so
this was not a timeout artifact. Over-approximation in `reached` cannot
cause a false SAFE (a superset with no query hit still means the true,
smaller set has no query hit either -- the same argument that justifies
trusting the generalized track's own SAFE verdicts). It *can* cause a
false UNSAFE: a query becoming satisfiable purely because of states
that were never actually reachable.

Because that's the one direction with real consequences, every
exact-track query hit is independently re-checked via
[`BoundedExplorer`](../src/pyhorn_bnd/explorer.py) -- a separate code
path with no dependency on `qe`, which SSA-unrolls the same rules
directly -- before it is ever reported as UNSAFE. An unconfirmed hit is
never surfaced as a counterexample; it's treated as inconclusive, the
relation involved is tainted for the rest of the run, and
`ForwardFixpointResult.qe_unsound_rejections` is incremented so a
caller (or `--debug`) can tell this happened. In practice this means
`--ff` can still report UNKNOWN in a case a naive reading of `qe`'s
output would have (wrongly) called UNSAFE -- which is the correct,
honest outcome: this module's own techniques (QE-based exact
projection, non-relational interval widening) were never suited to
proving *this* particular mod-based invariant anyway, bug or no bug.

## The generalized track (interval widening)

To help with the unbounded case, a second, *generalized* track runs in
parallel by default (disable with `--ff-no-generalization`). It starts
identical to the exact track, but once a variable's per-relation interval
bound has moved for `--ff-widening-delay` (default 2) consecutive rounds,
it is widened -- extrapolated all the way to ±infinity in one step, rather
than tracked incrementally. This is the classic Cousot–Cousot interval
widening operator from abstract interpretation.

Widening only ever *adds* states relative to the exact reachable set (a
bound only gets looser, never tighter), so by induction the generalized
track's formula is always a sound over-approximation of the true reachable
set. That has one direct consequence for how the two tracks are used:

- The generalized track reaching its **own** fixpoint with no query
  satisfiable against it is just as sound a SAFE proof as the exact
  fixpoint -- a superset with no bad state means the real, smaller set has
  no bad state either.
- A query becoming satisfiable against the **generalized** track is
  *never* treated as a counterexample on its own -- it may be a real bug,
  or it may be an artifact of the over-approximation (a state widening
  added that isn't actually reachable). Only a query hit against the
  **exact** track is ever reported as UNSAFE. The exact track keeps
  running, unmodified, in parallel for exactly this reason.

Interval widening is a **non-relational** abstraction: it captures each
variable's own range but drops any correlation between variables (`x == y`
degrades to independent bounds on `x` and on `y`). This means it cannot
prove invariants that are inherently relational -- e.g. two counters that
must always satisfy `y == 2*x` -- even though the exact track's true
reachable set does satisfy that relation. It's also only applied to
relations whose canonical variables are *all* Int/Real sorted; a relation
with any other sort (String, Array, Bool, ...) stays on the exact track
only, since "infinity" isn't a meaningful bound for those. Both are
standard, acknowledged limitations of interval abstraction -- a relational
domain (octagons, polyhedra) would recover the dropped correlations at real
added implementation complexity, which this module deliberately doesn't
take on.

## Taint propagation

QE can fail to fully resolve a formula (timeout, an unsupported theory
combination, a leftover quantifier). When that happens for a relation's
image in some round, that relation is marked **tainted**: every later round,
any rule whose source relation is tainted also produces an unknown (not
`False`) image, and taint propagates transitively to whatever depends on
it. This matters because an *untainted* empty/`False` image is a real,
trustworthy signal ("nothing reaches this precondition yet"), whereas a
tainted one just means "we don't actually know" -- treating the two the
same would let a QE failure masquerade as a premature, unsound fixpoint.
Once tainted, a relation can never report SAFE from its own fixpoint again
in that run (see `test_taint_propagates_and_blocks_a_premature_fixpoint` in
`tests/test_forward_fixpoint.py`).

## Implementation notes

The iteration is intentionally "simple": a direct Kleene iteration
processing every non-fact, non-query rule each round from a full snapshot
of the previous round, with no dependency ordering and no
incremental/interpolation tricks. It assumes only what the rest of this
codebase already assumes about the input: a normalized linear-CHC
`HornProgram` (linear CHC never joins two relations in one rule body).

Two timeouts bound the work: `--ff-timeout-ms` caps each individual Z3 QE
call, and `--ff-overall-timeout-s` caps the whole run's wall-clock budget
(checked between rounds). Everything inside a single QE call and its
immediate post-processing must stay fast on its own -- there is no way to
interrupt mid-call. In particular, the free-variable-leak check that
verifies QE actually eliminated what it was asked to walks the resulting
formula's AST directly by node id rather than using `z3.z3util.get_vars`
(a pure-Python utility that stringifies every subterm to deduplicate,
scales very badly on a formula that grows every round, and has no timeout
hook of its own) -- this was fixed after profiling showed it dominating
runtime by two orders of magnitude on an otherwise-fast benchmark. See
`test_growing_reachable_set_does_not_blow_up_wall_clock_time` for the
regression test.

## Seeding from something other than the literal init (`initial_seed`, `--ff-seeded`)

By default, round 0 is seeded from the literal, complete fact-rule
condition. `ForwardFixpoint.initial_seed` lets a caller override this,
per relation, with any formula -- as long as it's implied by the real
init (`Init ⇒ seed`, checked internally; violating this raises
`ValueError` rather than silently producing an unsound result). A seed
that's a superset of the real init (a single conjunct of it, say,
dropping other conjuncts entirely) is always valid this way.

This is sound in both directions, for reasons already established
elsewhere in this document:

- **SAFE** stays sound the same way the generalized track's SAFE
  verdicts do: a superset seed's own closure avoiding the query means
  the true, narrower init's closure avoids it too.
- **UNSAFE** needs no extra protection at all: `_confirm_counterexample`
  (see the CAUTION note above) already re-checks any candidate
  counterexample via `BoundedExplorer` against the program's *real* fact
  rules, entirely independent of whatever seed produced it -- so a
  counterexample only reachable from the part of an over-broad seed
  that isn't real gets caught and rejected there, the same as a
  `qe`-tactic over-approximation would be.

`--ff-seeded` (`ff_seeded.py`) is a concrete use of this: it extracts
the individual pieces of each relation's fact-rule condition -- the same
`SeedMiner`/`_boolean_seed_nodes` machinery Seed-Houdini already mines
candidates with, filtered to fact-rule provenance -- and tries each one
alone as `initial_seed`, in turn, stopping at the first SAFE (a
confirmed UNSAFE also stops immediately, being just as valid a proof of
the real program's unsafety as any other `--ff` counterexample). If none
work alone, it falls back to the full, literal init: today's plain `--ff`
behavior. This makes `--ff-seeded` never less capable than `--ff`, but
not strictly faster either -- trying several pieces that don't pan out
before reaching a working one, or the fallback, costs real time.

```bash
pyhorn-expl --ff-seeded input.smt2
```

Why a smaller seed can help at all, beyond just being a smaller problem:
a relation with variables a query genuinely doesn't depend on can still
make the *full* joint `qe` computation less able to find a proof it
finds once those variables are dropped -- not just slower. This was
measured directly, not assumed: a small benchmark with two variables
tied together by a threshold condition and two more the query never
touches converges cleanly to SAFE when seeded with just the first pair,
but the full four-variable computation reliably comes back UNKNOWN on
the same program (confirmed over repeated runs -- see
`test_initial_seed_that_drops_an_irrelevant_variable_still_proves_safe`).
It is *not*, however, a fix for the specific `qe`-tactic soundness issue
in the CAUTION note above, or a reliable way to route around it -- that
issue was reproduced on a formula mixing `%` with `If`, and swapping in
a smaller seed for the same mixed formula doesn't change the operators
involved. Confirmed on the actual case that motivated this feature: on
the mod/ite-based `dillig46` benchmark specifically, no single
fact-rule conjunct (x alone, y alone, z alone, or w alone) is enough --
the property genuinely needs two of them together -- so `--ff-seeded`
pays for several failed single-conjunct attempts before falling back to
the full init on that particular input, with no net win. This is an
honest limitation of trying single conjuncts specifically, not of the
underlying `initial_seed` mechanism, which works correctly for any sound
seed regardless of where it came from -- a caller with a way to
construct better combinations (multiple conjuncts together, a
Seed-Houdini candidate, a trace-derived formula) can pass any of them to
`initial_seed` directly, `--ff-seeded`'s single-conjunct strategy is just
the one built in today.

### A verified example

```smt2
(declare-var x Int)
(declare-var y Int)
(declare-rel inv (Int Int))
(declare-rel fail ())
(rule (=> (and (= x 0) (= y 0)) (inv x y)))
(rule (=> (and (inv x y) (< x 5)) (inv (+ x 1) y)))
(rule (=> (and (inv x y) (>= x 100)) fail))
(query fail)
```

```bash
$ pyhorn-expl --ff-seeded --debug irrelevant_y.smt2
...
tried 1 single-conjunct seed(s) before succeeding with: __inv_0 == 0
Success
```

`y` never affects `x`, and the single conjunct `x == 0` -- extracted
straight from the fact rule -- is already enough to prove `x < 100` on
its own, without ever needing to account for `y` at all.

## When to expect UNKNOWN

- A relational invariant (a fixed relationship between two or more
  variables, like `y == 2*x`) is provable by the *exact* track only if it
  literally stabilizes within `--ff-max-iterations` rounds -- the
  generalized track's interval widening drops variable correlations, so it
  cannot establish this class of property regardless of how many rounds it
  gets. There's no flag that fixes this; it's a fundamental limit of
  interval abstraction.
- Any relation with a non-Int/Real sort is exact-track-only and gets no
  benefit from widening -- an unbounded loop over such a relation will run
  out of iteration budget rather than converge.
- A tainted relation (see above) can still get UNSAFE reported normally if
  the exact track finds a real counterexample elsewhere, but can never
  itself yield a SAFE verdict from its own fixpoint.

`unknown` is not a claim that the input is unsafe -- only that neither
proof strategy converged in the given budget. Raising `--ff-max-iterations`
and/or `--ff-overall-timeout-s` may help for a genuinely-bounded system that
just needs more rounds; it will not help for the relational-invariant case
above -- but `--ff-houdini` (see [`ff_houdini.md`](ff_houdini.md)) might,
since Houdini's syntactic mining is exactly what covers relational facts
like `y == 2*x`.

## CLI reference

| Flag | Default | Meaning |
| --- | --- | --- |
| `--ff` | off | Enable the technique. Required for any `--ff-*` flag below to have an effect. |
| `--ff-seeded` | off | Run `--ff` seeded from individual fact-rule conjuncts, falling back to the full init -- see above. |
| `--ff-max-iterations` | 20 | Round budget before giving up with UNKNOWN. |
| `--ff-timeout-ms` | 10000 | Per-Z3-call timeout, in milliseconds. |
| `--ff-overall-timeout-s` | 30 | Overall wall-clock budget for the whole run, in seconds. |
| `--ff-no-generalization` | off (widening enabled) | Disable the generalized/widened track; exact iteration only. |
| `--ff-widening-delay` | 2 | Rounds a variable's interval bound must move before it gets widened. |

The `--ff-*` tuning flags require `--ff` itself -- passing one without it is
a usage error, not a silent no-op, since without `--ff` the run would
otherwise fall straight through to the default bounded-explorer pipeline
instead of running this technique at all. Note this usage error also exits
with code 2 (via `argparse`'s standard error handling), the same code as a
genuine UNKNOWN verdict below -- a script that only checks the exit code
can't distinguish the two; check stderr (a usage error prints a `usage:`
line and message there, an UNKNOWN verdict doesn't) if that matters.

### Exit codes and output

- `0` -- SAFE. Prints `Success`. With `--print-invariants`, also prints
  each relation's reachable-set formula (the actual proof, in the SAFE
  case exactly the reachable set).
- `1` -- UNSAFE. Prints `counterexample`, plus a model if one is available.
- `2` -- UNKNOWN. Prints `unknown`.
- `3` -- the input failed to parse.

With `--json`, a single JSON object is printed instead, with fields
`status`, `iterations`, `fixpoint_reached`, `message`, `violated_rule`
(the short form of the rule whose query fired, or `null`),
`counterexample`, and `qe_unsound_rejections` (see "A caution about the
exact track's own soundness" above -- normally 0; nonzero means at
least one candidate counterexample was independently rejected along the
way, so `status` may be UNKNOWN where a less careful reading of `qe`'s
raw output would have said UNSAFE). `--ff-seeded` adds two more:
`seed_used` (the winning conjunct as a string, or `null` if it fell back
to the full init) and `attempts` (how many single-conjunct seeds were
tried, including a failed one if the winner was the fallback).

### Example

```bash
$ pyhorn-expl --ff examples/seed_houdini/counter_safe.smt2
Success

$ pyhorn-expl --ff --ff-no-generalization --ff-max-iterations 5 examples/seed_houdini/counter_safe.smt2
unknown
```

The second invocation disables widening on a genuinely unbounded counter
with a small round budget, so the exact track alone doesn't have room to
either converge or find a bug -- an honest UNKNOWN, not a false negative.

`--print-invariants` also works with `--ff`, but be aware the printed
formula is the raw, unminimized reachable-set formula this module builds up
round by round -- since there's no dependency ordering or
incremental/interpolation tricks (see Implementation notes above), it's
typically a large nested disjunction rather than something a human would
write by hand, even when the underlying invariant is simple. It's still a
literal, checkable certificate; it just isn't meant to be read as
documentation the way a hand-guessed Seed-Houdini candidate is.
