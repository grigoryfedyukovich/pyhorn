; FEATURE: contains token "42" (digits)
(declare-var s String)
(declare-var t String)
(declare-rel inv (String String))
(declare-rel done (String))
(declare-rel fail ())

(rule (inv "42" "42"))
(rule
  (=> (and (inv s t) (= s t) (str.contains s "42") (< (str.len s) 8))
      (inv (str.++ "7" (str.++ s "8"))
           (str.++ "9" (str.++ t "0")))))
(rule
  (=> (and (inv s t) (not (= s t)) (str.contains s "42") (< (str.len s) 8))
      (inv (str.++ "7" (str.++ s "8"))
           (str.++ "9" (str.++ t "0")))))
(rule
  (=> (and (inv s t) (not (str.contains s "42")) (< (str.len s) 8))
      (inv (str.++ s "42") (str.++ t "42"))))
(rule
  (=> (inv s t)
      (done t)))
(rule
  (=> (and (done t) (not (str.contains t "42")))
      fail))
(query fail)
