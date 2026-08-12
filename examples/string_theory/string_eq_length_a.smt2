; FEATURE: string bridge  s=t → len(s)=len(t)
; inv diverges content but keeps equal lengths; done observes the two lengths.
; --seed-houdini: unknown    --seed-houdini --mut: Success
(declare-var s String)
(declare-var t String)
(declare-var n Int)
(declare-var m Int)
(declare-rel inv (String String))
(declare-rel done (Int Int))
(declare-rel fail ())

(rule (inv "a" "a"))
(rule
  (=> (and (inv s t) (< (str.len s) 3))
      (inv (str.++ s "x") (str.++ t "y"))))
(rule
  (=> (inv s t)
      (done (str.len s) (str.len t))))
(rule
  (=> (and (done n m) (not (= n m)))
      fail))
(query fail)
