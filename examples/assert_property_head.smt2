(set-logic HORN)

(declare-fun inv (Int) Bool)

(assert (inv 0))
(assert
  (forall ((x Int))
    (=> (and (inv x) (< x 2))
        (inv (+ x 1)))))
; This safety assertion is violated by the reachable state x = 2.
(assert
  (forall ((x Int))
    (=> (inv x)
        (<= x 1))))
(check-sat)
