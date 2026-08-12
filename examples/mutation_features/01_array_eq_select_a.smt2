; FEATURE: sort-agnostic equality substitution (arrays)
; a=b holds at init but is broken by stores at index 1.
; (= (select a 0) 0) is mined; --mut rewrites it under a=b to
; (= (select b 0) 0), which is inductive and needed for done.
; Trace templates do not cover array contents, so --trace-houdini alone fails.
(declare-var a (Array Int Int))
(declare-var b (Array Int Int))
(declare-var i Int)
(declare-var v Int)
(declare-rel inv ((Array Int Int) (Array Int Int) Int))
(declare-rel done (Int))
(declare-rel fail ())

(rule (inv ((as const (Array Int Int)) 0)
           ((as const (Array Int Int)) 0)
           0))
(rule
  (=> (and (inv a b i) (= a b) (= (select a 0) 0))
      (inv (store a 1 5) (store b 1 7) i)))
(rule
  (=> (and (inv a b i) (not (= a b)))
      (inv (store a 1 5) (store b 1 7) i)))
(rule
  (=> (inv a b i)
      (done (select b 0))))
(rule
  (=> (and (done v) (not (= v 0)))
      fail))
(query fail)
