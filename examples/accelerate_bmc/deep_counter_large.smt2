; Same shape as deep_counter_small.smt2, but with a threshold high enough
; that unrolling to it is impractical -- only meant to be run WITH
; --accelerate-bmc, to demonstrate that search depth is independent of the
; real iteration count a counterexample needs.
(set-logic HORN)
(declare-rel inv (Int Int))
(declare-rel fail ())
(declare-var x0 Int) (declare-var x1 Int)
(declare-var y0 Int) (declare-var y1 Int)
(rule (=> (and (= x1 0) (= y1 0)) (inv x1 y1)))
(rule (=> (and (inv x0 y0) (< x0 1000000000) (= x1 (+ x0 1)) (= y1 y0)) (inv x1 y1)))
(rule (=> (and (inv x0 y0) (>= x0 1000000000)) fail))
(query fail)
