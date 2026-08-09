; User-supplied candidates for ../real_arithmetic/counter_safe.smt2.
; Mirrors ../seed_houdini/counter_safe_candidates.smt2 exactly, retyped
; from Int to Real, so this candidate pair exercises the same "confirmed
; real" (bounded-reachable) removal path via --validate-candidates.
;
; Run with:
;   chc-bounded-explorer ../real_arithmetic/counter_safe.smt2 \
;     --cands real_counter_safe_candidates.smt2 \
;     --validate-candidates --debug --print-invariants
;
; `x <= 10.0` is the fact that actually makes the query clause valid.
; `x = 0.0` is a deliberately too-tight candidate: true only at the initial
; fact, so MultiHoudini drops it as soon as the self-loop advances x to
; 1.0. It exists purely so --validate-candidates has something real to
; confirm (reachable at depth 2, the step right after the fact).
(define-fun inv ((x Real)) Bool
  (and (<= x 10.0)
       (= x 0.0)))
