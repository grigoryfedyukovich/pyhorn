; Single self-loop, outer (non-ite) guard. Threshold kept small (50) so the
; *unaccelerated* baseline is still fast enough to run in CI -- see
; deep_counter_large.smt2 for a threshold where only the accelerated search
; is tractable at all.
(set-logic HORN)
(declare-rel inv (Int Int))
(declare-rel fail ())
(declare-var x0 Int) (declare-var x1 Int)
(declare-var y0 Int) (declare-var y1 Int)
(rule (=> (and (= x1 0) (= y1 0)) (inv x1 y1)))
(rule (=> (and (inv x0 y0) (< x0 50) (= x1 (+ x0 1)) (= y1 y0)) (inv x1 y1)))
(rule (=> (and (inv x0 y0) (>= x0 50)) fail))
(query fail)
