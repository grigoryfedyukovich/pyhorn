; Digit strings track an integer counter via str.from_int / str.to_int.
(set-logic HORN)
(declare-var s String)
(declare-var n Int)
(declare-rel inv (String Int))
(declare-rel fail ())

(rule (inv "0" 0))
(rule
  (=> (and (inv s n) (< n 3))
      (inv (str.from_int (+ n 1)) (+ n 1))))
(rule
  (=> (and (inv s n) (not (= (str.to_int s) n)))
      fail))
(query fail)
