; FEATURE: array equality substitution (variant: nonzero default, different stores)
(declare-var a (Array Int Int))
(declare-var b (Array Int Int))
(declare-var i Int)
(declare-var v Int)
(declare-rel inv ((Array Int Int) (Array Int Int) Int))
(declare-rel done (Int))
(declare-rel fail ())

(rule (inv ((as const (Array Int Int)) 3)
           ((as const (Array Int Int)) 3)
           0))
(rule
  (=> (and (inv a b i) (= a b) (= (select a 0) 3))
      (inv (store a 2 9) (store b 2 8) i)))
(rule
  (=> (and (inv a b i) (not (= a b)))
      (inv (store a 2 9) (store b 2 8) i)))
(rule
  (=> (inv a b i)
      (done (select b 0))))
(rule
  (=> (and (done v) (not (= v 3)))
      fail))
(query fail)
