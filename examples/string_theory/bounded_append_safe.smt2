; Ported from pyhorn-bounded-explorer 0.0.15's
; examples/string_length_literature/bounded_append_safe.smt2 (a divergent
; branch that added literature-derived String+Int length benchmarks but
; does not include this branch's --cands / --validate-candidates feature).
; Reused here specifically to exercise that feature over pure String state:
; see examples/cands/string_bounded_append_candidates.smt2.
;
; Bounded append loop: the guard prevents the buffer from exceeding length 8.
(declare-fun inv (String) Bool)
(assert (inv ""))
(assert
  (forall ((s String))
    (=> (and (inv s) (< (str.len s) 8))
        (inv (str.++ s "x")))))
(assert
  (forall ((s String))
    (=> (and (inv s) (> (str.len s) 8))
        false)))
(check-sat)
