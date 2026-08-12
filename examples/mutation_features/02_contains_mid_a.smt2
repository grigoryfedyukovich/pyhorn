; FEATURE: contains with asymmetric growth rates / longer bound
(declare-var s String)
(declare-var t String)
(declare-rel inv (String String))
(declare-rel done (String))
(declare-rel fail ())

(rule (inv "mn" "mn"))
(rule
  (=> (and (inv s t) (= s t) (str.contains s "mn") (< (str.len s) 10))
      (inv (str.++ "0" (str.++ s "1"))
           (str.++ "2" (str.++ t "3")))))
(rule
  (=> (and (inv s t) (not (= s t)) (str.contains s "mn") (< (str.len s) 10))
      (inv (str.++ "0" (str.++ s "1"))
           (str.++ "2" (str.++ t "3")))))
(rule
  (=> (and (inv s t) (not (str.contains s "mn")) (< (str.len s) 10))
      (inv (str.++ s "mn") (str.++ t "mn"))))
(rule
  (=> (inv s t)
      (done t)))
(rule
  (=> (and (done t) (not (str.contains t "mn")))
      fail))
(query fail)
