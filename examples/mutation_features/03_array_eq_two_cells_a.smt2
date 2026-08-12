; FEATURE: equality substitution on a second cell
; Stores diverge at index 2; cell 0 and the tracked index stay in sync via mut.
(declare-var a (Array Int Int))
(declare-var b (Array Int Int))
(declare-var i Int)
(declare-var v Int)
(declare-rel inv ((Array Int Int) (Array Int Int) Int))
(declare-rel done (Int))
(declare-rel fail ())

(rule (inv ((as const (Array Int Int)) 1)
           ((as const (Array Int Int)) 1)
           0))
(rule
  (=> (and (inv a b i) (= a b) (= (select a 0) 1))
      (inv (store (store a 0 1) 2 10)
           (store (store b 0 1) 2 11)
           i)))
(rule
  (=> (and (inv a b i) (not (= a b)))
      (inv (store (store a 0 1) 2 10)
           (store (store b 0 1) 2 11)
           i)))
(rule
  (=> (inv a b i)
      (done (select b 0))))
(rule
  (=> (and (done v) (not (= v 1)))
      fail))
(query fail)
