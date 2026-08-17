(set-logic HORN)

; PhaseFit benchmark: threshold 4, phase-1 anchor 2, phase-2 increment 3.
; The safety proof requires the cross-variable invariant y = z after the threshold.
; The error is stated through congruence of an uninterpreted function so the
; useful equality is not literally present in the error predicate.

(declare-rel inv (Int Int Int))
(declare-rel fail ())
(declare-fun f (Int) Int)
(declare-var x0 Int)
(declare-var x1 Int)
(declare-var y0 Int)
(declare-var y1 Int)
(declare-var z0 Int)
(declare-var z1 Int)

(rule (=> (and (= x1 0) (= y1 2) (= z1 2)) (inv x1 y1 z1)))

(rule
  (=>
    (and
      (inv x0 y0 z0)
      (= x1 (ite (< x0 4) (+ x0 1) x0))
      (= y1 (ite (< x0 4) 2 (+ y0 3)))
      (= z1 (ite (< x0 4) 2 (+ z0 3))))
    (inv x1 y1 z1)))

(rule
  (=>
    (and (inv x0 y0 z0) (>= x0 4) (not (= (f y0) (f z0))))
    fail))

(query fail)
