; A real-valued counter reaches exactly 1 after four quarter steps.
(set-logic HORN)
(declare-rel inv (Real))
(declare-rel fail ())
(declare-var x Real)

(rule (inv 0.0))
(rule
  (=> (and (inv x) (<= x (/ 3.0 4.0)))
      (inv (+ x (/ 1.0 4.0)))))
(rule (=> (and (inv x) (>= x 1.0)) fail))
(query fail)
