; Mixed String/Int state with length tracking.
(set-logic HORN)
(declare-var s String)
(declare-var n Int)
(declare-rel inv (String Int))
(declare-rel fail ())

(rule (inv "" 0))
(rule
  (=> (and (inv s n) (< n 3))
      (inv (str.++ s "x") (+ n 1))))
(rule
  (=> (and (inv s n) (not (= (str.len s) n)))
      fail))
(query fail)
