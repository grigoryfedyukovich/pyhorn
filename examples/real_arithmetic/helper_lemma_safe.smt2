; Real analog of the Int "helper lemma" fixture used by
; tests/test_candidate_validation_cli.py: two correlated state components
; (x counts up, y counts down) where a candidate mentioning only y, supplied
; alone via --cands, is genuinely true throughout but is not locally
; inductive by itself -- MultiHoudini's per-rule induction check treats x as
; completely unconstrained (no active candidate mentions it), so it can
; posit an unreachable pre-state (y = 1) consistent only with the lone
; candidate, and finds a spurious counterexample-to-induction from it. The
; candidate is real, but bound-checking never finds a falsifying state
; because x is actually capped at 5.0, so y never drops below 95.0.
;
; See examples/cands/real_helper_lemma_candidates.smt2.
(declare-var x Real)
(declare-var y Real)
(declare-rel inv (Real Real))
(declare-rel fail ())

(rule (inv 0.0 100.0))
(rule (=> (and (inv x y) (< x 5.0)) (inv (+ x 1.0) (- y 1.0))))
(rule (=> (and (inv x y) (>= x 5.0) (< y 90.0)) fail))
(query fail)
