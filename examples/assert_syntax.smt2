(set-logic HORN)

(declare-fun inv (Int) Bool)

(assert (inv 0))
(assert
  (forall ((x Int))
    (=> (and (inv x) (< x 2))
        (inv (+ x 1)))))
(assert
  (forall ((x Int))
    (=> (and (inv x) (>= x 2))
        false)))
(check-sat)
