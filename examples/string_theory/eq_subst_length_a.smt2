; FEATURE: equality substitution  under s=t rewrite n=len(s) → n=len(t)
(declare-var s String)
(declare-var t String)
(declare-var n Int)
(declare-var k Int)
(declare-rel inv (String String Int))
(declare-rel done (Int String))
(declare-rel fail ())

(rule (inv "a" "a" 1))
; mention both equalities so SeedMiner records them; transition breaks s=t
(rule
  (=> (and (inv s t n)
           (= s t)
           (= n (str.len s))
           (< n 4))
      (inv (str.++ s "x") (str.++ t "y") (+ n 1))))
(rule
  (=> (and (inv s t n)
           (not (= s t))
           (= n (str.len s))
           (< n 4))
      (inv (str.++ s "x") (str.++ t "y") (+ n 1))))
(rule
  (=> (and (inv s t n)
           (not (= n (str.len s)))
           (< n 4))
      (inv (str.++ s "x") (str.++ t "y") (+ n 1))))
(rule
  (=> (inv s t n)
      (done n t)))
(rule
  (=> (and (done k t) (not (= k (str.len t))))
      fail))
(query fail)
