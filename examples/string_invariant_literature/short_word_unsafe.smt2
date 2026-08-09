; Reachable bad word via a single rewrite step (bounded cex).
(declare-fun inv (String) Bool)

(assert (inv "a"))
(assert
  (forall ((s String))
    (=> (and (inv s) (= s "a"))
        (inv (str.++ s "b")))))
(assert
  (forall ((s String))
    (=> (and (inv s) (= s "ab"))
        false)))
(check-sat)
