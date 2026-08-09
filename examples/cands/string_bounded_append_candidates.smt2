; User-supplied candidates for ../string_theory/bounded_append_safe.smt2.
; `(<= (str.len s) 8)` is the fact that actually makes the safety property
; valid. `(= s "")` is a deliberately too-tight candidate: true only at the
; initial fact, so MultiHoudini drops it as soon as the self-loop appends
; the first character -- exercising --validate-candidates' "confirmed
; real" path (reachable at depth 2) over pure String state.
;
; Run with:
;   chc-bounded-explorer ../string_theory/bounded_append_safe.smt2 \
;     --cands string_bounded_append_candidates.smt2 \
;     --validate-candidates --debug --print-invariants
(define-fun inv ((s String)) Bool
  (and (<= (str.len s) 8)
       (= s "")))
