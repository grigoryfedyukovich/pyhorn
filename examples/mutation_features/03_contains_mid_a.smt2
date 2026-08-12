; FEATURE: contains with three-char token "xyz"
(declare-var s String)
(declare-var t String)
(declare-rel inv (String String))
(declare-rel done (String))
(declare-rel fail ())

(rule (inv "xyz" "xyz"))
(rule
  (=> (and (inv s t) (= s t) (str.contains s "xyz") (< (str.len s) 9))
      (inv (str.++ "p" (str.++ s "q"))
           (str.++ "r" (str.++ t "s")))))
(rule
  (=> (and (inv s t) (not (= s t)) (str.contains s "xyz") (< (str.len s) 9))
      (inv (str.++ "p" (str.++ s "q"))
           (str.++ "r" (str.++ t "s")))))
(rule
  (=> (and (inv s t) (not (str.contains s "xyz")) (< (str.len s) 9))
      (inv (str.++ s "xyz") (str.++ t "xyz"))))
(rule
  (=> (inv s t)
      (done t)))
(rule
  (=> (and (done t) (not (str.contains t "xyz")))
      fail))
(query fail)
