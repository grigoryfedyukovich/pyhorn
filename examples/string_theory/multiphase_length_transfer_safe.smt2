; Ported from pyhorn-bounded-explorer 0.0.15's
; examples/string_length_literature/multiphase_length_transfer_safe.smt2.
; Two predicates (fill/drain) sharing a String/Int length invariant across
; a phase transition -- additional multi-predicate String+Int coverage for
; the bounded explorer and SeedMiner/MultiHoudini.
;
; Two control phases preserve a shared string-length counter.
(declare-fun fill (String Int) Bool)
(declare-fun drain (String Int) Bool)
(assert (fill "" 0))
(assert
  (forall ((s String) (n Int))
    (=> (and (fill s n) (< n 3))
        (fill (str.++ s "x") (+ n 1)))))
(assert
  (forall ((s String) (n Int))
    (=> (and (fill s n) (= n 3))
        (drain s n))))
(assert
  (forall ((s String) (n Int))
    (=> (and (drain s n) (> n 0))
        (drain (str.substr s 1 (- (str.len s) 1)) (- n 1)))))
(assert
  (forall ((s String) (n Int))
    (=> (and (fill s n) (not (= (str.len s) n)))
        false)))
(assert
  (forall ((s String) (n Int))
    (=> (and (drain s n) (not (= (str.len s) n)))
        false)))
(check-sat)
