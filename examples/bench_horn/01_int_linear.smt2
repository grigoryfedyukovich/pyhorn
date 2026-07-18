; Extracted from bench_horn/s_triv_08.smt2.
; Coverage: Int state, constants in relation arguments, equality, and negation.

(declare-rel inv (Int Int))
(declare-var x Int)
(declare-var x1 Int)
(declare-var y Int)
(declare-var y1 Int)

(declare-rel fail ())

(rule (inv 0 0))

(rule (=> (inv 1 y) (inv x 1)
  )
)

(rule (=> (and (inv x y) (not (= x y))) fail))

(query fail :print-certificate true)
