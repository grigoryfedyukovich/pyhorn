; String state in Z3 fixedpoint command syntax.
(declare-var s String)
(declare-rel inv (String))
(declare-rel fail ())

(rule (inv ""))
(rule
  (=> (and (inv s) (< (str.len s) 3))
      (inv (str.++ s "a"))))
(rule
  (=> (and (inv s) (str.contains s "b"))
      fail))
(query fail)
