; re.union, re.range, and re.++ membership over a growing word.
(declare-var s String)
(declare-rel inv (String))
(declare-rel fail ())

(rule (inv ""))
(rule
  (=> (and (inv s) (< (str.len s) 3))
      (inv (str.++ s "a"))))
(rule
  (=> (and (inv s) (< (str.len s) 3))
      (inv (str.++ s "1"))))
(rule
  (=> (and (inv s)
           (not (str.in_re s
                  (re.*
                    (re.union
                      (re.range "a" "z")
                      (re.range "0" "9"))))))
      fail))
(query fail)
