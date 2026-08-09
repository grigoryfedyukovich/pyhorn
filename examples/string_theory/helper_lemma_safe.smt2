; String analog of examples/real_arithmetic/helper_lemma_safe.smt2 /
; the Int "helper lemma" fixture in tests/test_candidate_validation_cli.py.
; Two correlated string state components: s grows by one character per
; step (5 steps max, guarded by str.len s < 5), t shrinks by one character
; per step (str.substr drops its first character). A candidate mentioning
; only t, supplied alone via --cands, is globally true (t never gets
; shorter than 5 characters) but is not locally inductive by itself:
; MultiHoudini's per-rule induction check treats s as unconstrained (no
; active candidate mentions it), so it can posit t = a single character --
; consistent with the lone candidate but never actually reachable -- and
; finds a spurious counterexample-to-induction from it.
;
; See examples/cands/string_helper_lemma_candidates.smt2.
(declare-var s String)
(declare-var t String)
(declare-rel inv (String String))
(declare-rel fail ())

(rule (inv "" "aaaaaaaaaa"))
(rule
  (=> (and (inv s t) (< (str.len s) 5))
      (inv (str.++ s "x") (str.substr t 1 (- (str.len t) 1)))))
(rule (=> (and (inv s t) (>= (str.len s) 5) (< (str.len t) 4)) fail))
(query fail)
