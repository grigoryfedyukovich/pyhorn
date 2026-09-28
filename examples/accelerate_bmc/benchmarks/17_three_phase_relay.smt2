(set-logic HORN)
(declare-rel inv (Int Int Int Int))
(declare-rel fail ())
(declare-var x0 Int) (declare-var x1 Int)
(declare-var a0 Int) (declare-var a1 Int)
(declare-var b0 Int) (declare-var b1 Int)
(declare-var c0 Int) (declare-var c1 Int)
(rule (=> (and (= x1 0) (= a1 0) (= b1 0) (= c1 0)) (inv x1 a1 b1 c1)))
(rule
  (=>
    (and
      (inv x0 a0 b0 c0)
      (= x1 (+ x0 1))
      (= a1 (ite (< x0 200000000) (+ a0 1) a0))
      (= b1 (ite (< x0 200000000) b0 (ite (< x0 500000000) (+ b0 1) b0)))
      (= c1 (ite (< x0 500000000) c0 (+ c0 1))))
    (inv x1 a1 b1 c1)))
(rule (=> (and (inv x0 a0 b0 c0) (>= c0 900000000)) fail))
(query fail)
