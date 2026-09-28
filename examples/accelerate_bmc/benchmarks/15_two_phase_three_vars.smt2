(set-logic HORN)
(declare-rel inv (Int Int Int))
(declare-rel fail ())
(declare-var x0 Int) (declare-var x1 Int)
(declare-var y0 Int) (declare-var y1 Int)
(declare-var z0 Int) (declare-var z1 Int)
(rule (=> (and (= x1 0) (= y1 0) (= z1 0)) (inv x1 y1 z1)))
(rule
  (=>
    (and
      (inv x0 y0 z0)
      (= x1 (ite (< x0 400000000) (+ x0 1) x0))
      (= y1 (ite (< x0 400000000) (+ y0 2) y0))
      (= z1 (ite (< x0 400000000) z0 (+ z0 1))))
    (inv x1 y1 z1)))
(rule (=> (and (inv x0 y0 z0) (>= z0 900000000)) fail))
(query fail)
