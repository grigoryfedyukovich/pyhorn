; Unicode and doubled-quote SMT-LIB string literal handling.
(set-logic HORN)
(declare-rel inv (String))
(declare-rel fail ())
(rule (inv "\u{3bb}""x"))
(rule (=> (and (inv "\u{3bb}""x") false) fail))
(query fail)
