; Literature-derived from HornStr Example 1 (CAV 2025).
; Two tokens r and b move synchronously through empty n positions.
; The bad language has b at the left border and r at the right border.
(set-logic HORN)
(declare-fun inv (String) Bool)

(assert
  (forall ((vi String))
    (=> (str.in_re vi
          (re.++ (str.to_re "rn")
                 (re.* (str.to_re "nn"))
                 (str.to_re "b")))
        (inv vi))))

(assert
  (forall ((vi String) (vo String) (a String) (b String) (c String))
    (=> (and (inv vi)
             (= vi (str.++ a "rn" b "nb" c))
             (= vo (str.++ a "nr" b "bn" c)))
        (inv vo))))

(assert
  (forall ((vi String) (vo String) (a String) (b String) (c String))
    (=> (and (inv vi)
             (= vi (str.++ a "nb" b "rn" c))
             (= vo (str.++ a "bn" b "nr" c)))
        (inv vo))))

(assert
  (forall ((vi String) (vo String) (a String) (b String))
    (=> (and (inv vi)
             (= vi (str.++ a "rb" b))
             (= vo (str.++ a "br" b)))
        (inv vo))))

(assert
  (forall ((vi String))
    (=> (and (inv vi)
             (str.in_re vi
               (re.++ (str.to_re "b")
                      (re.* (str.to_re "n"))
                      (str.to_re "r"))))
        false)))
(check-sat)
