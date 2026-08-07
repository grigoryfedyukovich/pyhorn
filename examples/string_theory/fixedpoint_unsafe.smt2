; Bounded exploration reaches the exact string "aaa".
(set-logic HORN)
(declare-var s String)
(declare-rel inv (String))
(declare-rel fail ())

(rule (inv ""))
(rule
  (=> (and (inv s) (< (str.len s) 3))
      (inv (str.++ s "a"))))
(rule
  (=> (and (inv s) (= s "aaa"))
      fail))
(query fail)
