; FEATURE: concat length additivity (variant)
(declare-var s String)
(declare-var t String)
(declare-var u String)
(declare-var n Int)
(declare-var a Int)
(declare-var b Int)
(declare-rel inv (String String String))
(declare-rel done (Int Int Int))
(declare-rel fail ())

(rule (inv "" "go" "go"))
(rule
  (=> (and (inv s t u) (= u (str.++ s t)) (< (str.len u) 5))
      (inv (str.++ s "p") (str.++ t "q") (str.++ u "pq"))))
(rule
  (=> (and (inv s t u) (not (= u (str.++ s t))) (< (str.len u) 5))
      (inv (str.++ s "p") (str.++ t "q") (str.++ u "pq"))))
(rule
  (=> (inv s t u)
      (done (str.len u) (str.len s) (str.len t))))
(rule
  (=> (and (done n a b) (not (= n (+ a b))))
      fail))
(query fail)
