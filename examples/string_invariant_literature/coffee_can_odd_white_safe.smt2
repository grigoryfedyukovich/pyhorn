; Gries coffee-can rewriting over B (black) and W (white).
; Starting from WWWB, the final one-bean state cannot be B because the
; parity of the number of W symbols is invariant.
(declare-fun inv (String) Bool)
(assert (inv "WWWB"))

(assert
  (forall ((vi String) (vo String) (x String) (y String))
    (=> (and (inv vi)
             (= vi (str.++ x "BB" y))
             (= vo (str.++ x "B" y)))
        (inv vo))))
(assert
  (forall ((vi String) (vo String) (x String) (y String))
    (=> (and (inv vi)
             (= vi (str.++ x "WW" y))
             (= vo (str.++ x "B" y)))
        (inv vo))))
(assert
  (forall ((vi String) (vo String) (x String) (y String))
    (=> (and (inv vi)
             (= vi (str.++ x "BW" y))
             (= vo (str.++ x "W" y)))
        (inv vo))))
(assert
  (forall ((vi String) (vo String) (x String) (y String))
    (=> (and (inv vi)
             (= vi (str.++ x "WB" y))
             (= vo (str.++ x "W" y)))
        (inv vo))))
(assert (=> (inv "B") false))
(check-sat)
