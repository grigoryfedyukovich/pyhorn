; Literature-derived from HornStr Example 2 and Hofstadter's MU puzzle.
; MU is not reachable from MI under the four rewrite rules.
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

(assert (=> (inv "MU") false))
(check-sat)
