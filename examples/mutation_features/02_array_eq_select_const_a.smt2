; FEATURE: array equality substitution (const array of 5; diverge at index 3)
(declare-var a (Array Int Int))
(declare-var b (Array Int Int))
(declare-var i Int)
(declare-var v Int)
(declare-rel inv ((Array Int Int) (Array Int Int) Int))
(declare-rel done (Int))
(declare-rel fail ())

(rule (inv ((as const (Array Int Int)) 5)
           ((as const (Array Int Int)) 5)
           0))
(rule
  (=> (and (inv a b i) (= a b) (= (select a 0) 5))
      (inv (store a 3 1) (store b 3 2) i)))
(rule
  (=> (and (inv a b i) (not (= a b)))
      (inv (store a 3 1) (store b 3 2) i)))
(rule
  (=> (inv a b i)
      (done (select b 0))))
(rule
  (=> (and (done v) (not (= v 5)))
      fail))
(query fail)
