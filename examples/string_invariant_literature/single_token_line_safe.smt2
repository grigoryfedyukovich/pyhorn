; A single token T moves right through empty N positions.
; The safety property excludes configurations with two tokens.
(set-logic HORN)
(declare-fun inv (String) Bool)
(assert (inv "TNNNN"))
(assert
  (forall ((vi String) (vo String) (x String) (y String))
    (=> (and (inv vi)
             (= vi (str.++ x "TN" y))
             (= vo (str.++ x "NT" y)))
        (inv vo))))
(assert
  (forall ((vi String))
    (=> (and (inv vi)
             (str.in_re vi
               (re.++ (re.* re.allchar)
                      (str.to_re "T")
                      (re.* re.allchar)
                      (str.to_re "T")
                      (re.* re.allchar))))
        false)))
(check-sat)
