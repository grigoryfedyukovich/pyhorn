; Extracted from bench_horn/s_triv_10.smt2.
; Coverage: Boolean relation state and a bare Boolean body constraint.

(declare-rel inv (Bool))
(declare-var x Bool)

(declare-rel fail ())

(rule (inv false))

(rule (=> (inv x) (inv x)))

(rule (=> (and (inv x) x) fail))

(query fail :print-certificate true)
