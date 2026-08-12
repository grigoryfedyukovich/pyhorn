; FEATURE: string bridge  prefixof("ab",s) → len(s)≥2
; Prefix is mined from a guard, broken by prepending; length bound is not.
(declare-var s String)
(declare-var n Int)
(declare-rel inv (String))
(declare-rel done (Int))
(declare-rel fail ())

(rule (inv "ab"))
(rule
  (=> (and (inv s) (str.prefixof "ab" s) (< (str.len s) 5))
      (inv (str.++ "x" s))))
(rule
  (=> (and (inv s) (not (str.prefixof "ab" s)) (< (str.len s) 5))
      (inv (str.++ "x" s))))
(rule
  (=> (inv s)
      (done (str.len s))))
(rule
  (=> (and (done n) (< n 2))
      fail))
(query fail)
