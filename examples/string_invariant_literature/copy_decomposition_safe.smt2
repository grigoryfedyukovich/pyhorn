; Character-by-character copy. The inductive word equation is:
; original = output ++ remaining.
(set-logic HORN)
(declare-fun inv (String String String) Bool)
(assert (forall ((original String)) (inv original original "")))
(assert
  (forall ((original String) (remaining String) (output String))
    (=> (and (inv original remaining output)
             (> (str.len remaining) 0))
        (inv original
             (str.substr remaining 1 (- (str.len remaining) 1))
             (str.++ output (str.at remaining 0))))))
(assert
  (forall ((original String) (remaining String) (output String))
    (=> (and (inv original remaining output)
             (not (= original (str.++ output remaining))))
        false)))
(check-sat)
