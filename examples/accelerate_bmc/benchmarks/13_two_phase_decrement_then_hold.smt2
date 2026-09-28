(set-logic HORN)
(declare-rel inv (Int Int))
(declare-rel fail ())
(declare-var x0 Int) (declare-var x1 Int)
(declare-var p0 Int) (declare-var p1 Int)
(rule (=> (and (= x1 400000000) (= p1 0)) (inv x1 p1)))
(rule
  (=>
    (and
      (inv x0 p0)
      (= x1 (ite (> x0 0) (- x0 1) x0))
      (= p1 (ite (> x0 0) p0 (+ p0 1))))
    (inv x1 p1)))
(rule (=> (and (inv x0 p0) (>= p0 900000000)) fail))
(query fail)
