; Ported from pyhorn-bounded-explorer 0.0.17's examples/
; string_length_literature/copy_length_conservation_safe.smt2
; (a divergent branch that added literature-derived String+Int str.len
; benchmarks but does not include this branch's --cands /
; --validate-candidates / --mut features). Reused here to complete this
; suite; see docs/string_length_constraints.md and
; tools/audit_string_length_benchmarks.py.
;
; Character-copy loop preserving total length and a ghost input length.
(set-logic HORN)
(declare-fun inv (String String Int) Bool)
(assert
  (forall ((input String))
    (inv input "" (str.len input))))
(assert
  (forall ((remaining String) (output String) (total Int))
    (=> (and (inv remaining output total)
             (> (str.len remaining) 0))
        (inv (str.substr remaining 1 (- (str.len remaining) 1))
             (str.++ output (str.at remaining 0))
             total))))
(assert
  (forall ((remaining String) (output String) (total Int))
    (=> (and (inv remaining output total)
             (not (= (+ (str.len remaining) (str.len output)) total)))
        false)))
(check-sat)
