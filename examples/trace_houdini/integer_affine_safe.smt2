; Trace models lie on y = 2*x.  The trace miner should recover the affine equality.
(set-logic HORN)
(declare-fun inv (Int Int) Bool)
(assert (inv 0 0))
(assert
  (forall ((x Int) (y Int))
    (=> (inv x y)
        (inv (+ x 1) (+ y 2)))))
(assert
  (forall ((x Int) (y Int))
    (=> (and (inv x y) (not (= y (* 2 x))))
        false)))
(check-sat)
