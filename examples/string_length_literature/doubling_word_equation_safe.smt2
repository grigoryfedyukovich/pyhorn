; Ported from pyhorn-bounded-explorer 0.0.17's examples/
; string_length_literature/doubling_word_equation_safe.smt2
; (a divergent branch that added literature-derived String+Int str.len
; benchmarks but does not include this branch's --cands /
; --validate-candidates / --mut features). Reused here to complete this
; suite; see docs/string_length_constraints.md and
; tools/audit_string_length_benchmarks.py.
;
; Word equation y = x ++ x implies |y| = 2*|x| and remains true under growth.
(set-logic HORN)
(declare-fun inv (String String) Bool)
(assert
  (forall ((x String))
    (inv x (str.++ x x))))
(assert
  (forall ((x String) (y String))
    (=> (inv x y)
        (inv (str.++ x "a") (str.++ y "aa")))))
(assert
  (forall ((x String) (y String))
    (=> (and (inv x y)
             (not (= (str.len y) (* 2 (str.len x)))))
        false)))
(check-sat)
