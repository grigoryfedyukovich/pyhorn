; Three counters that step together, starting 2 apart: x=n, y=n+1, z=n+2 for
; every reachable n. Built to exercise --mut's inequality-transitivity chain
; (x<=y and y<=z give x<=z) directly, via examples/cands/transitive_bounds_candidates.smt2,
; which supplies only x<=y and y<=z -- not x<=z, which is the safety property.
;
; Note: Z3's own linear-arithmetic reasoning combines x<=y and y<=z into
; x<=z for free during final certification once both are simultaneously
; retained hypotheses for the same check -- so this file's safety property
; is provable via --cands alone too, without --mut. What --mut demonstrably
; adds here is the derived x<=z candidate itself showing up as a first-class,
; independently-retained member of the pool (see the --mut test that checks
; for it in --json output), which is what a later rule needing x and z alone
; (with y no longer in scope, e.g. after a multi-predicate transition) would
; actually require.
(declare-var x Int)
(declare-var y Int)
(declare-var z Int)
(declare-rel inv (Int Int Int))
(declare-rel fail ())

(rule (inv 0 1 2))
(rule (=> (inv x y z) (inv (+ x 1) (+ y 1) (+ z 1))))
(rule (=> (and (inv x y z) (> x z)) fail))
(query fail)
