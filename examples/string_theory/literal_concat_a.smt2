; FEATURE: literal concat propagation
; start holds the pins; inv is entered only with u = s++t already applied.
(declare-var s String)
(declare-var t String)
(declare-var u String)
(declare-rel start (String String))
(declare-rel inv (String String String))
(declare-rel sink (String))
(declare-rel fail ())

(rule (start "ab" "cd"))
(rule
  (=> (and (start s t) (= s "ab") (= t "cd"))
      (inv s t (str.++ s t))))
(rule
  (=> (and (inv s t u) (= s "ab") (= t "cd") (= u (str.++ s t)))
      (inv "XX" t u)))
(rule
  (=> (and (inv s t u) (not (= s "ab")))
      (inv s t u)))
(rule
  (=> (inv s t u)
      (sink u)))
(rule
  (=> (and (sink u) (not (= u "abcd")))
      fail))
(query fail)
