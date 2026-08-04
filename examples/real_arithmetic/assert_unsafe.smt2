; Pure SMT-LIB HORN assertions over Real.
(set-logic HORN)
(declare-fun inv (Real) Bool)

(assert (inv (/ 1.0 2.0)))
(assert
  (forall ((x Real))
    (=> (and (inv x) (< x 2.0))
        (inv (+ x (/ 1.0 2.0))))))
(assert
  (forall ((x Real))
    (=> (and (inv x) (>= x 2.0))
        false)))
(check-sat)
