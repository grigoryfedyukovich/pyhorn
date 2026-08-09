; Reachable variant of the MU system: MI -> MIU by rule 1.
(declare-fun inv (String) Bool)
(assert (inv "MI"))
(assert
  (forall ((vi String) (vo String) (x String))
    (=> (and (inv vi)
             (= vi (str.++ x "I"))
             (= vo (str.++ x "IU")))
        (inv vo))))
(assert
  (forall ((vi String) (vo String) (x String))
    (=> (and (inv vi)
             (= vi (str.++ "M" x))
             (= vo (str.++ "M" x x)))
        (inv vo))))
(assert
  (forall ((vi String) (vo String) (x String) (y String))
    (=> (and (inv vi)
             (= vi (str.++ x "III" y))
             (= vo (str.++ x "U" y)))
        (inv vo))))
(assert
  (forall ((vi String) (vo String) (x String) (y String))
    (=> (and (inv vi)
             (= vi (str.++ x "UU" y))
             (= vo (str.++ x y)))
        (inv vo))))
(assert (=> (inv "MIU") false))
(check-sat)
