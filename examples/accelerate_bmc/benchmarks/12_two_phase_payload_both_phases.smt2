(set-logic HORN)
(declare-rel inv (Int Int))
(declare-rel fail ())
(declare-var c0 Int) (declare-var c1 Int)
(declare-var p0 Int) (declare-var p1 Int)
(rule (=> (and (= c1 0) (= p1 0)) (inv c1 p1)))
(rule
  (=>
    (and
      (inv c0 p0)
      (= c1 (ite (< c0 300000000) (+ c0 1) c0))
      (= p1 (+ p0 1)))
    (inv c1 p1)))
(rule (=> (and (inv c0 p0) (>= p0 900000000)) fail))
(query fail)
