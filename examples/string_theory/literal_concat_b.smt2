; FEATURE: literal concat propagation (variant)
(declare-var s String)
(declare-var t String)
(declare-var u String)
(declare-rel start (String String))
(declare-rel inv (String String String))
(declare-rel sink (String))
(declare-rel fail ())

(rule (start "xy" "z!"))
(rule
  (=> (and (start s t) (= s "xy") (= t "z!"))
      (inv s t (str.++ s t))))
(rule
  (=> (and (inv s t u) (= s "xy") (= t "z!") (= u (str.++ s t)))
      (inv s "??" u)))
(rule
  (=> (and (inv s t u) (not (= t "z!")))
      (inv s t u)))
(rule
  (=> (inv s t u)
      (sink u)))
(rule
  (=> (and (sink u) (not (= u "xyz!")))
      fail))
(query fail)
