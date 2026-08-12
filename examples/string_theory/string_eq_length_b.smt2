; FEATURE: string bridge equal lengths (longer start, different alphabet)
(declare-var s String)
(declare-var t String)
(declare-var n Int)
(declare-var m Int)
(declare-rel inv (String String))
(declare-rel done (Int Int))
(declare-rel fail ())

(rule (inv "go" "go"))
(rule
  (=> (and (inv s t) (< (str.len s) 5))
      (inv (str.++ s "A") (str.++ t "B"))))
(rule
  (=> (inv s t)
      (done (str.len s) (str.len t))))
(rule
  (=> (and (done n m) (not (= n m)))
      fail))
(query fail)
