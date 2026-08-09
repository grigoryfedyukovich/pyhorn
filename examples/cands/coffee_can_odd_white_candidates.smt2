; Hand-derived candidate for ../string_invariant_literature/coffee_can_odd_white_safe.smt2.
;
; SeedMiner's syntactic mining cannot synthesize this invariant at all --
; see tests/test_string_invariant_literature.py's
; test_syntactic_seedminer_does_not_overclaim_hard_regular_problems, which
; confirms --seed-houdini gives `unknown` on this file. SMT-LIB's String
; theory has no character-counting primitive, so "the number of W symbols
; is odd" has to be expressed as a regular-language membership instead.
; Parity of a single symbol's count over a 2-symbol alphabet IS a regular
; property (a 2-state DFA: EVEN/ODD, flip on W, stay on B), so this is
; expressible -- SeedMiner just has no way to invent it, since it only
; manipulates subterms already appearing in the rule/query text, and no
; regex anywhere in the source file encodes this.
;
; Derived by hand via standard state-elimination on that 2-state DFA:
;   B* W (B* W B* W)* B*
; i.e.: any number of B's, then a W (the first "odd" flip), then any
; number of (B* W B* W) blocks (each of which flips parity twice, net
; zero), then any number of trailing B's. Verified exhaustively against a
; brute-force reference (not just a handful of hand-checked cases) over
; every string of length 0-11 over {W, B}: zero mismatches against "odd
; number of W" for all 4095 of them -- the LANGUAGE this regex describes
; is correct.
;
; The candidate does NOT, however, get this file to Success in practice --
; checked directly, not assumed. --cands parses it correctly (one
; candidate, one predicate) and MultiHoudini never rejects it as wrong
; (removed=0), but the very first induction check attempted (rule r1,
; `BB -> B`, which does not involve W at all and is content-irrelevant to
; this invariant) times out before ever reaching certification. That rules
; out this specific regex, or W-counting, as the cause: what's expensive
; is checking regex-membership invariance across an
; `x ++ OLD ++ y -> x ++ NEW ++ y` rewrite at an existentially-split
; position, for any regex, in this Z3 build. Every rewrite rule in this
; file (and in the other hard examples in string_invariant_literature/
; that share this shape) hits the same wall. See
; tests/test_candidate_validation_theories.py's
; test_cands_hand_derived_candidate_also_times_out for the confirmed
; result and docs/candidate_validation_theory_coverage.md for the fuller
; writeup. Left here anyway: the derivation and its independent language
; verification are correct and may be useful against a Z3 build without
; this limitation.
;
; Run with:
;   pyhorn-expl --cands coffee_can_odd_white_candidates.smt2 \
;     --debug --print-invariants \
;     ../string_invariant_literature/coffee_can_odd_white_safe.smt2
(define-fun inv ((s String)) Bool
  (str.in_re s
    (re.++
      (re.* (str.to_re "B"))
      (str.to_re "W")
      (re.*
        (re.++
          (re.* (str.to_re "B"))
          (str.to_re "W")
          (re.* (str.to_re "B"))
          (str.to_re "W")))
      (re.* (str.to_re "B")))))
