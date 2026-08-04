; Mixed integer/real state with an explicit to_real coercion.
(set-logic HORN)
(declare-rel inv (Int Real))
(declare-rel fail ())
(declare-var i Int)
(declare-var x Real)

(rule (inv 0 0.0))
(rule
  (=> (and (inv i x) (< i 4))
      (inv (+ i 1) (+ x (/ 1.0 2.0)))))
(rule (=> (and (inv i x) (> x (to_real i))) fail))
(query fail)
