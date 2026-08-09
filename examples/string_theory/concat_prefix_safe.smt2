; Multi-step concatenation preserves a fixed prefix.
(declare-var s String)
(declare-rel inv (String))
(declare-rel fail ())

(rule (inv "ab"))
(rule
  (=> (and (inv s) (< (str.len s) 5))
      (inv (str.++ s "c"))))
(rule
  (=> (and (inv s) (not (str.prefixof "ab" s)))
      fail))
(query fail)
