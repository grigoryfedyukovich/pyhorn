(set-logic HORN)

(declare-var x Int)
(declare-rel inv (Int))
(declare-rel fail ())

(rule (inv 0))
(rule (=> (and (inv x) (< x 2)) (inv (+ x 1))))
(rule (=> (and (inv x) (>= x 2)) fail))
(query fail)
