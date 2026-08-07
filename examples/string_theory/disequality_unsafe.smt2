; Bounded counterexample driven by string disequality.
(set-logic HORN)
(declare-var s String)
(declare-rel inv (String))
(declare-rel fail ())

(rule (inv "ok"))
(rule
  (=> (and (inv s) (= s "ok"))
      (inv "bad")))
(rule
  (=> (and (inv s) (not (= s "ok")))
      fail))
(query fail)
