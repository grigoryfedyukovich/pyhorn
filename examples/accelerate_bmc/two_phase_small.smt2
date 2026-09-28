; Branching self-loop (a single ite-based rule with two phases): while
; below the threshold, x increments and y is held at 0; once at or above
; it, x is held fixed and y increments instead. Exercises per-branch
; acceleration, including the "guard is n-invariant once you're in this
; branch" path (phase 2's x >= threshold condition never changes once x
; stops moving) alongside the "monotonic crossover" path (phase 1's
; x < threshold).
(set-logic HORN)
(declare-rel inv (Int Int))
(declare-rel fail ())
(declare-var x0 Int) (declare-var x1 Int)
(declare-var y0 Int) (declare-var y1 Int)
(rule (=> (and (= x1 0) (= y1 0)) (inv x1 y1)))
(rule
  (=>
    (and
      (inv x0 y0)
      (= x1 (ite (< x0 30) (+ x0 1) x0))
      (= y1 (ite (< x0 30) y0 (+ y0 1))))
    (inv x1 y1)))
(rule (=> (and (inv x0 y0) (>= y0 30)) fail))
(query fail)
