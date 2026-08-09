; User-supplied candidates for ../mixed_theories/real_string_safe.smt2.
; `(= total (to_real (str.len log)))` is the fact that actually makes the
; query clause valid. `(= log "")` is a deliberately too-tight candidate,
; true only at the initial fact -- exercises --validate-candidates'
; "confirmed real" path (reachable at depth 2) over a Real+String
; predicate signature.
;
; Run with:
;   chc-bounded-explorer ../mixed_theories/real_string_safe.smt2 \
;     --cands real_string_candidates.smt2 \
;     --validate-candidates --debug --print-invariants
(define-fun inv ((total Real) (log String)) Bool
  (and (= total (to_real (str.len log)))
       (= log "")))
