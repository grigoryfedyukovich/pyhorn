; Every reachable word is a prefix of a fixed target; Seed-Houdini friendly.
(declare-fun inv (String) Bool)

(assert (inv ""))
(assert
  (forall ((s String))
    (=> (and (inv s) (str.prefixof (str.++ s "a") "aaa"))
        (inv (str.++ s "a")))))
(assert
  (forall ((s String))
    (=> (inv s) (str.prefixof s "aaa"))))
(check-sat)
