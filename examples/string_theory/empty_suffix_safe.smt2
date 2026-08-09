; Empty string is a suffix of every reachable state.
(declare-var s String)
(declare-rel inv (String))
(declare-rel fail ())

(rule (inv ""))
(rule
  (=> (and (inv s) (< (str.len s) 4))
      (inv (str.++ s "z"))))
(rule
  (=> (and (inv s) (not (str.suffixof "" s)))
      fail))
(query fail)
