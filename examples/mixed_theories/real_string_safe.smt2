; A Real accumulator kept in exact lockstep with a String log's length via
; `to_real`. Neither examples/real_arithmetic/ nor examples/string_theory/
; has a Real+String combination (both combine with Int instead); this file
; specifically exercises that pairing across parsing, SSA, the bounded
; explorer, SeedMiner/MultiHoudini, and --cands/--validate-candidates.
;
; See examples/cands/real_string_candidates.smt2.
(declare-var total Real)
(declare-var log String)
(declare-rel inv (Real String))
(declare-rel fail ())

(rule (inv 0.0 ""))
(rule
  (=> (and (inv total log) (< total 5.0))
      (inv (+ total 1.0) (str.++ log "x"))))
(rule (=> (and (inv total log) (> total (to_real (str.len log)))) fail))
(query fail)
