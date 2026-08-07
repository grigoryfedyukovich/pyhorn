; Restricted alphabet stream: only "a" is appended, so raw '<' never appears.
; Local safety property suitable for SeedMiner + MultiHoudini.
(set-logic HORN)
(declare-fun inv (String) Bool)

(assert (inv ""))
(assert
  (forall ((s String))
    (=> (and (inv s) (< (str.len s) 5))
        (inv (str.++ s "a")))))
(assert
  (forall ((s String))
    (=> (inv s) (not (str.contains s "<")))))
(check-sat)
