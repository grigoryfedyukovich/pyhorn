; Ported from pyhorn-bounded-explorer 0.0.15's
; examples/string_length_literature/password_policy_safe.smt2. Combines
; regular-expression membership with a length range in one property --
; additional String+regex+Int(length) combination coverage beyond
; examples/string_theory/regex_safe.smt2 and mixed_string_int_safe.smt2.
;
; Password construction: alphanumeric content with a length range [8, 12].
(declare-fun inv (String) Bool)
(define-fun alnum () RegLan
  (re.union (re.range "a" "z") (re.range "0" "9")))
(assert (inv "a0aaaaaa"))
(assert
  (forall ((s String))
    (=> (and (inv s) (< (str.len s) 12))
        (inv (str.++ s "a")))))
(assert
  (forall ((s String))
    (=> (and (inv s) (< (str.len s) 12))
        (inv (str.++ s "0")))))
(assert
  (forall ((s String))
    (=> (and (inv s)
             (or (< (str.len s) 8)
                 (> (str.len s) 12)
                 (not (str.in_re s (re.* alnum)))))
        false)))
(check-sat)
