; Arrays with String elements remain sort-correct through SSA and Houdini.
(declare-var a (Array Int String))
(declare-var a1 (Array Int String))
(declare-var i Int)
(declare-rel inv ((Array Int String) Int))
(declare-rel fail ())

(rule (inv ((as const (Array Int String)) "") 0))
(rule
  (=> (and (inv a i)
           (< i 2)
           (= a1 (store a i "ok")))
      (inv a1 (+ i 1))))
(rule
  (=> (and (inv a i)
           (> i 0)
           (not (= (select a 0) "ok")))
      fail))
(query fail)
