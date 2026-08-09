; Three-way combination: an Int step counter, a Real accumulator, and a
; String log, all kept in lockstep in a single predicate's signature.
; Extends examples/mixed_theories/real_string_safe.smt2 with an explicit
; Int component so all three theories occur together in one relation.
;
; See examples/cands/int_real_string_candidates.smt2.
(declare-var n Int)
(declare-var total Real)
(declare-var log String)
(declare-rel inv (Int Real String))
(declare-rel fail ())

(rule (inv 0 0.0 ""))
(rule
  (=> (and (inv n total log) (< n 5))
      (inv (+ n 1) (+ total 1.0) (str.++ log "x"))))
(rule
  (=> (and (inv n total log)
           (or (not (= n (str.len log)))
               (> total (to_real n))))
      fail))
(query fail)
