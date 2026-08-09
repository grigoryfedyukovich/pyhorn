; Regular-expression membership remains a native Z3 string constraint.
(declare-var s String)
(declare-rel inv (String))
(declare-rel fail ())

(rule (inv ""))
(rule
  (=> (and (inv s) (< (str.len s) 4))
      (inv (str.++ s "a"))))
(rule
  (=> (and (inv s)
           (not (str.in_re s (re.* (str.to_re "a")))))
      fail))
(query fail)
