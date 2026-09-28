; No inductive rule at all (a straight-line acyclic program) -- accelerate
; should be a clean no-op here: nothing to accelerate, and the returned
; program/result must be identical to a plain run.
(set-logic HORN)
(declare-rel p (Int))
(declare-rel q (Int))
(declare-rel fail ())
(declare-var x Int)
(rule (=> (= x 0) (p x)))
(rule (=> (p x) (q (+ x 1))))
(rule (=> (and (q x) (>= x 1)) fail))
(query fail)
