; User-supplied candidate for ../string_theory/helper_lemma_safe.smt2.
; Deliberately supplies ONLY a weak, uncorrelated bound on t's length --
; nothing here ties it to s -- so MultiHoudini's local induction check
; treats s as unconstrained and can posit t as a single character,
; consistent with the lone candidate but never actually reachable (t only
; ever shrinks from 10 characters to 5 in this program).
; --validate-candidates should report this as "potentially promising".
;
; Run with:
;   chc-bounded-explorer ../string_theory/helper_lemma_safe.smt2 \
;     --cands string_helper_lemma_candidates.smt2 \
;     --validate-candidates --debug
(define-fun inv ((s String) (t String)) Bool
  (>= (str.len t) 1))
