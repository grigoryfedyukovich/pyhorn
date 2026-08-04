; Integer-indexed array with exact real-valued elements.
(set-logic HORN)
(declare-rel inv ((Array Int Real) Int))
(declare-rel fail ())
(declare-var a (Array Int Real))
(declare-var a1 (Array Int Real))
(declare-var i Int)
(declare-var j Int)

(rule (inv a 0))
(rule
  (=> (and (inv a i)
           (= a1 (store a i (/ (to_real i) 2.0))))
      (inv a1 (+ i 1))))
(rule
  (=> (and (inv a i)
           (<= 0 j)
           (< j i)
           (not (= (select a j) (/ (to_real j) 2.0))))
      fail))
(query fail)
