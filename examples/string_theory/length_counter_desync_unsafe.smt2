; Ported from pyhorn-bounded-explorer 0.0.15's
; examples/string_length_literature/length_counter_desync_unsafe.smt2.
; A buggy ghost counter (append two characters, increment by only one)
; gives the bounded explorer a String+Int counterexample to find --
; complements examples/string_theory/disequality_unsafe.smt2.
;
; Buggy counter update: append two characters but increment the counter by one.
(declare-fun inv (String Int) Bool)
(assert (inv "" 0))
(assert
  (forall ((s String) (n Int))
    (=> (inv s n)
        (inv (str.++ s "xx") (+ n 1)))))
(assert
  (forall ((s String) (n Int))
    (=> (and (inv s n) (not (= (str.len s) n)))
        false)))
(check-sat)
