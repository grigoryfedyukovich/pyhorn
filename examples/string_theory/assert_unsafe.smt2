; Pure SMT-LIB HORN assertions with String operations.
(set-logic HORN)
(declare-fun inv (String) Bool)

(assert (inv ""))
(assert
  (forall ((s String))
    (=> (and (inv s) (< (str.len s) 2))
        (inv (str.++ s "b")))))
(assert
  (forall ((s String))
    (=> (and (inv s) (= s "bb"))
        false)))
(check-sat)
