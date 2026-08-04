; Integer state whose use of / introduces exact Real arithmetic and to_real.
(set-logic HORN)
(declare-rel inv (Int Int))
(declare-rel fail ())
(declare-var a Int)
(declare-var b Int)

(rule (inv 2 1))
(rule (=> (and (inv a b) (not (= b (/ a 2)))) fail))
(query fail)
