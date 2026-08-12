; FEATURE: string bridge  u=s++t → len(u)=len(s)+len(t)
(declare-var s String)
(declare-var t String)
(declare-var u String)
(declare-var n Int)
(declare-var a Int)
(declare-var b Int)
(declare-rel inv (String String String))
(declare-rel done (Int Int Int))
(declare-rel fail ())

(rule (inv "a" "b" "ab"))
(rule
  (=> (and (inv s t u) (= u (str.++ s t)) (< (str.len u) 6))
      (inv (str.++ s "x") (str.++ t "y") (str.++ u "xy"))))
(rule
  (=> (and (inv s t u) (not (= u (str.++ s t))) (< (str.len u) 6))
      (inv (str.++ s "x") (str.++ t "y") (str.++ u "xy"))))
(rule
  (=> (inv s t u)
      (done (str.len u) (str.len s) (str.len t))))
(rule
  (=> (and (done n a b) (not (= n (+ a b))))
      fail))
(query fail)
