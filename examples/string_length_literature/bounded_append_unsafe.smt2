; Ported from pyhorn-bounded-explorer 0.0.17's examples/
; string_length_literature/bounded_append_unsafe.smt2
; (a divergent branch that added literature-derived String+Int str.len
; benchmarks but does not include this branch's --cands /
; --validate-candidates / --mut features). Reused here to complete this
; suite; see docs/string_length_constraints.md and
; tools/audit_string_length_benchmarks.py.
;
; Off-by-one buffer guard: appending two characters can cross the bound.
(set-logic HORN)
(declare-fun inv (String) Bool)
(assert (inv ""))
(assert
  (forall ((s String))
    (=> (and (inv s) (<= (str.len s) 2))
        (inv (str.++ s "xx")))))
(assert
  (forall ((s String))
    (=> (and (inv s) (> (str.len s) 3))
        false)))
(check-sat)
