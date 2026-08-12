; FEATURE: string bridge  suffixof("yz",s) → len(s)≥2
(declare-var s String)
(declare-var n Int)
(declare-rel inv (String))
(declare-rel done (Int))
(declare-rel fail ())

(rule (inv "yz"))
(rule
  (=> (and (inv s) (str.suffixof "yz" s) (< (str.len s) 5))
      (inv (str.++ s "x"))))
(rule
  (=> (and (inv s) (not (str.suffixof "yz" s)) (< (str.len s) 5))
      (inv (str.++ s "x"))))
(rule
  (=> (inv s)
      (done (str.len s))))
(rule
  (=> (and (done n) (< n 2))
      fail))
(query fail)
