; FEATURE: string equality substitution of str.contains
; "xy" stays in the middle while ends grow differently on s and t.
; Trace cannot use common-prefix/suffix (samples share neither).
; --mut rewrites (str.contains s "xy") under s=t into (str.contains t "xy").
(declare-var s String)
(declare-var t String)
(declare-rel inv (String String))
(declare-rel done (String))
(declare-rel fail ())

(rule (inv "xy" "xy"))
(rule
  (=> (and (inv s t) (= s t) (str.contains s "xy") (< (str.len s) 8))
      (inv (str.++ "a" (str.++ s "b"))
           (str.++ "c" (str.++ t "d")))))
(rule
  (=> (and (inv s t) (not (= s t)) (str.contains s "xy") (< (str.len s) 8))
      (inv (str.++ "a" (str.++ s "b"))
           (str.++ "c" (str.++ t "d")))))
(rule
  (=> (and (inv s t) (not (str.contains s "xy")) (< (str.len s) 8))
      (inv (str.++ s "xy") (str.++ t "xy"))))
(rule
  (=> (inv s t)
      (done t)))
(rule
  (=> (and (done t) (not (str.contains t "xy")))
      fail))
(query fail)
