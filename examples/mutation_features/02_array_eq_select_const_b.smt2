; FEATURE: array equality substitution (const array of -1; diverge at index 4)
(declare-var a (Array Int Int))
(declare-var b (Array Int Int))
(declare-var i Int)
(declare-var v Int)
(declare-rel inv ((Array Int Int) (Array Int Int) Int))
(declare-rel done (Int))
(declare-rel fail ())

(rule (inv ((as const (Array Int Int)) (- 1))
           ((as const (Array Int Int)) (- 1))
           0))
(rule
  (=> (and (inv a b i) (= a b) (= (select a 0) (- 1)))
      (inv (store a 4 0) (store b 4 9) i)))
(rule
  (=> (and (inv a b i) (not (= a b)))
      (inv (store a 4 0) (store b 4 9) i)))
(rule
  (=> (inv a b i)
      (done (select b 0))))
(rule
  (=> (and (done v) (not (= v (- 1))))
      fail))
(query fail)
