; SeedMiner obtains x <= 10 from the negated query condition.
(declare-var x Int)
(declare-rel inv (Int))
(declare-rel fail ())
(rule (inv 0))
(rule (=> (and (inv x) (< x 10)) (inv (+ x 1))))
(rule (=> (and (inv x) (> x 10)) fail))
(query fail)
