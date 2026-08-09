; User-supplied candidates for ../mixed_theories/int_real_string_safe.smt2.
; The first two conjuncts are the facts that actually make the query
; clause valid. `(= log "")` is a deliberately too-tight candidate, true
; only at the initial fact -- exercises --validate-candidates' "confirmed
; real" path (reachable at depth 2) over an Int+Real+String signature.
;
; Run with:
;   chc-bounded-explorer ../mixed_theories/int_real_string_safe.smt2 \
;     --cands int_real_string_candidates.smt2 \
;     --validate-candidates --debug --print-invariants
(define-fun inv ((n Int) (total Real) (log String)) Bool
  (and (= n (str.len log))
       (= total (to_real n))
       (= log "")))
