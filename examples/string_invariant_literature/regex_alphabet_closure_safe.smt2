; Regular-language closure with complement: only a and b are appended.
(declare-fun inv (String) Bool)
(assert (inv ""))
(assert (forall ((s String)) (=> (inv s) (inv (str.++ s "a")))))
(assert (forall ((s String)) (=> (inv s) (inv (str.++ s "b")))))
(assert
  (forall ((s String))
    (=> (and (inv s)
             (str.in_re s
               (re.comp
                 (re.*
                   (re.union (str.to_re "a") (str.to_re "b"))))))
        false)))
(check-sat)
