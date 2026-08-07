; Fixedpoint syntax with regular-expression membership.
(declare-var s String)
(declare-rel inv (String))
(declare-rel fail ())
(rule (inv ""))
(rule (=> (and (inv s) (< (str.len s) 3)) (inv (str.++ s "x"))))
(rule
  (=> (and (inv s)
           (not (str.in_re s (re.* (str.to_re "x")))))
      fail))
(query fail)
