; Ported from pyhorn-bounded-explorer 0.0.17's examples/
; string_length_literature/sliding_window_safe.smt2
; (a divergent branch that added literature-derived String+Int str.len
; benchmarks but does not include this branch's --cands /
; --validate-candidates / --mut features). Reused here to complete this
; suite; see docs/string_length_constraints.md and
; tools/audit_string_length_benchmarks.py.
;
; A fixed-width sliding window remains exactly four characters long.
(set-logic HORN)
(declare-fun inv (String Int String) Bool)
(assert
  (forall ((input String))
    (=> (>= (str.len input) 4)
        (inv input 0 (str.substr input 0 4)))))
(assert
  (forall ((input String) (start Int) (window String))
    (=> (and (inv input start window)
             (< (+ start 4) (str.len input)))
        (inv input (+ start 1) (str.substr input (+ start 1) 4)))))
(assert
  (forall ((input String) (start Int) (window String))
    (=> (and (inv input start window)
             (not (= (str.len window) 4)))
        false)))
(check-sat)
