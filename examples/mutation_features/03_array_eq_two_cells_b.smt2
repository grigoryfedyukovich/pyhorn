; FEATURE: equality substitution two-cells (variant defaults)
(declare-var a (Array Int Int))
(declare-var b (Array Int Int))
(declare-var i Int)
(declare-var v Int)
(declare-rel inv ((Array Int Int) (Array Int Int) Int))
(declare-rel done (Int))
(declare-rel fail ())

(rule (inv ((as const (Array Int Int)) 2)
           ((as const (Array Int Int)) 2)
           0))
(rule
  (=> (and (inv a b i) (= a b) (= (select a 0) 2))
      (inv (store (store a 0 2) 3 20)
           (store (store b 0 2) 3 21)
           i)))
(rule
  (=> (and (inv a b i) (not (= a b)))
      (inv (store (store a 0 2) 3 20)
           (store (store b 0 2) 3 21)
           i)))
(rule
  (=> (inv a b i)
      (done (select b 0))))
(rule
  (=> (and (done v) (not (= v 2)))
      fail))
(query fail)
