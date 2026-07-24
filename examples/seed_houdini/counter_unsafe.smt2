; No conjunction of the syntactic candidates proves this unsafe system.
(declare-var x Int)
(declare-rel inv (Int))
(declare-rel fail ())
(rule (inv 0))
(rule (=> (inv x) (inv (+ x 1))))
(rule (=> (and (inv x) (>= x 2)) fail))
(query fail)
