; User-supplied candidate for ../real_arithmetic/helper_lemma_safe.smt2.
; Deliberately supplies ONLY the weak, uncorrelated bound on y -- the
; correlating fact (y = 100.0 - x) is intentionally withheld -- so
; MultiHoudini's local induction check treats x as unconstrained and finds
; a counterexample-to-induction that no real execution can ever produce.
; --validate-candidates should report this as "potentially promising"
; (not found within the bound), not "confirmed real".
;
; Run with:
;   chc-bounded-explorer ../real_arithmetic/helper_lemma_safe.smt2 \
;     --cands real_helper_lemma_candidates.smt2 \
;     --validate-candidates --debug
(define-fun inv ((x Real) (y Real)) Bool
  (>= y 1.0))
