(set-logic HORN)
(declare-rel inv (Int Int))
(declare-rel fail ())
(declare-var x0 Int) (declare-var x1 Int)
(declare-var y0 Int) (declare-var y1 Int)
(rule (=> (and (= x1 0) (= y1 0)) (inv x1 y1)))
(rule
  (=>
    (and
      (inv x0 y0)
      (= x1 (ite (<= x0 400000000) (+ x0 1) x0))
      (= y1 (ite (<= x0 400000000) y0 (+ y0 1))))
    (inv x1 y1)))
(rule (=> (and (inv x0 y0) (> y0 900000000)) fail))
(query fail)
