; Nonlinear real arithmetic is preserved for Z3; bounded exploration finds a CEX.
(set-logic HORN)
(declare-rel inv (Real))
(declare-rel fail ())
(declare-var x Real)

(rule (inv (- 2.0)))
(rule (=> (inv x) (inv (* x x))))
(rule (=> (and (inv x) (> x 3.0)) fail))
(query fail)
