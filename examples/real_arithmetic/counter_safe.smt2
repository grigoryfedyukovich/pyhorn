; Real analog of examples/seed_houdini/counter_safe.smt2, used to exercise
; --cands / --validate-candidates over Real arithmetic: see
; examples/cands/real_counter_safe_candidates.smt2, which supplies one
; correct invariant and one deliberately too-tight candidate for
; MultiHoudini to drop.
;
; NOT a literal retype of the Int original: Int's `x < 10` guard becomes
; `x <= 9.0` here, one step below the bound, rather than `x < 10.0`. Reals
; are dense, and MultiHoudini's induction check for a candidate x <= 10.0
; only has that candidate itself (not the true reachable set) to
; characterize the pre-state, so a strict `x < 10.0` guard would let it
; pick a fractional pre-state such as x = 9.5 -- satisfying both the
; candidate and the guard, yet stepping to 10.5 and falsely refuting an
; invariant that every actual (integer-valued) execution of this loop
; satisfies. The non-strict, one-lower guard closes that gap: x <= 9.0
; forces x + 1.0 <= 10.0 for every real x satisfying it, not just integers.
(declare-var x Real)
(declare-rel inv (Real))
(declare-rel fail ())

(rule (inv 0.0))
(rule (=> (and (inv x) (<= x 9.0)) (inv (+ x 1.0))))
(rule (=> (and (inv x) (> x 10.0)) fail))
(query fail)
