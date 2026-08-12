; FEATURE: contains mid-substring (variant token "PQ")
(declare-var s String)
(declare-var t String)
(declare-rel inv (String String))
(declare-rel done (String))
(declare-rel fail ())

(rule (inv "PQ" "PQ"))
(rule
  (=> (and (inv s t) (= s t) (str.contains s "PQ") (< (str.len s) 8))
      (inv (str.++ "x" (str.++ s "y"))
           (str.++ "u" (str.++ t "v")))))
(rule
  (=> (and (inv s t) (not (= s t)) (str.contains s "PQ") (< (str.len s) 8))
      (inv (str.++ "x" (str.++ s "y"))
           (str.++ "u" (str.++ t "v")))))
(rule
  (=> (and (inv s t) (not (str.contains s "PQ")) (< (str.len s) 8))
      (inv (str.++ s "PQ") (str.++ t "PQ"))))
(rule
  (=> (inv s t)
      (done t)))
(rule
  (=> (and (done t) (not (str.contains t "PQ")))
      fail))
(query fail)
