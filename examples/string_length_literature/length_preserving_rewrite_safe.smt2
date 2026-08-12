; Ported from pyhorn-bounded-explorer 0.0.17's examples/
; string_length_literature/length_preserving_rewrite_safe.smt2
; (a divergent branch that added literature-derived String+Int str.len
; benchmarks but does not include this branch's --cands /
; --validate-candidates / --mut features). Reused here to complete this
; suite; see docs/string_length_constraints.md and
; tools/audit_string_length_benchmarks.py.
;
; Local replacement of two characters by two characters preserves length.
(set-logic HORN)
(declare-fun inv (String Int) Bool)
(assert
  (forall ((s String))
    (inv s (str.len s))))
(assert
  (forall ((s String) (n Int) (left String) (right String))
    (=> (and (inv s n)
             (= s (str.++ left "ab" right)))
        (inv (str.++ left "cd" right) n))))
(assert
  (forall ((s String) (n Int))
    (=> (and (inv s n) (not (= (str.len s) n)))
        false)))
(check-sat)
