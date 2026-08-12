; FEATURE: contains token "++" (non-letter alphabet)
(declare-var s String)
(declare-var t String)
(declare-rel inv (String String))
(declare-rel done (String))
(declare-rel fail ())

(rule (inv "++" "++"))
(rule
  (=> (and (inv s t) (= s t) (str.contains s "++") (< (str.len s) 8))
      (inv (str.++ "A" (str.++ s "B"))
           (str.++ "C" (str.++ t "D")))))
(rule
  (=> (and (inv s t) (not (= s t)) (str.contains s "++") (< (str.len s) 8))
      (inv (str.++ "A" (str.++ s "B"))
           (str.++ "C" (str.++ t "D")))))
(rule
  (=> (and (inv s t) (not (str.contains s "++")) (< (str.len s) 8))
      (inv (str.++ s "++") (str.++ t "++"))))
(rule
  (=> (inv s t)
      (done t)))
(rule
  (=> (and (done t) (not (str.contains t "++")))
      fail))
(query fail)
