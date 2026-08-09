; examples/mixed_theories/real_string_safe.smt2 and int_real_string_safe.smt2
; are both easy: SeedMiner mines the exact linear equality/coercion needed
; and MultiHoudini finds it immediately. This file is the mixed-theory
; counterpart to examples/string_invariant_literature/coffee_can_odd_white_safe.smt2:
; safe, but this tool genuinely cannot prove it.
;
; It is the Gries coffee-can rewriting system, unchanged, with an orthogonal
; Int step counter threaded through the signature so String is combined
; with Int in one relation (Int String), not just String alone. The counter
; is easy on its own (SeedMiner finds n >= 0 immediately) and is otherwise
; irrelevant to the property being checked -- the bad-state check still
; only inspects the String component, so this remains exactly as hard as
; the parent example: the parity of the number of `W` symbols is invariant
; under all four rewrite rules (each changes the W-count by 0 or -2), so
; the single-bean state "B" (zero W symbols, even) is unreachable from
; "WWWB" (three W symbols, odd). SMT-LIB's String theory has no native
; character-counting primitive, so that parity fact would have to be
; expressed as a regular-language invariant (a regex or DFA encoding
; "odd number of W"); parity IS a regular property in principle, and a
; human can derive that regex correctly (see
; examples/cands/coffee_can_odd_white_candidates.smt2, which does, and
; verifies the derivation exhaustively against a brute-force reference).
; But supplying it via --cands does NOT get this class of problem to
; Success in this Z3 build -- tried directly against the pure-String
; parent example, not assumed: the induction check for even the simplest,
; W-irrelevant rewrite rule (`BB -> B`) times out before certification is
; ever reached. So this remains a case where --cands doesn't rescue
; --seed-houdini either, just for a different reason: not a mining
; capability gap, but a solver-performance limit on checking
; regex-membership invariance across an `x ++ OLD ++ y -> x ++ NEW ++ y`
; rewrite at an existentially-split position. See
; tests/test_string_invariant_literature.py::test_syntactic_seedminer_does_not_overclaim_hard_regular_problems
; for the pure-String original's confirmed `unknown` result via
; --seed-houdini, tests/test_candidate_validation_theories.py::test_cands_hand_derived_candidate_also_times_out
; for the --cands attempt's confirmed result, and
; tests/test_mixed_theories_hard.py for this file's own --seed-houdini
; result.
(declare-fun inv (Int String) Bool)
(assert (inv 0 "WWWB"))

(assert
  (forall ((n Int) (vi String) (vo String) (x String) (y String))
    (=> (and (inv n vi)
             (= vi (str.++ x "BB" y))
             (= vo (str.++ x "B" y)))
        (inv (+ n 1) vo))))
(assert
  (forall ((n Int) (vi String) (vo String) (x String) (y String))
    (=> (and (inv n vi)
             (= vi (str.++ x "WW" y))
             (= vo (str.++ x "B" y)))
        (inv (+ n 1) vo))))
(assert
  (forall ((n Int) (vi String) (vo String) (x String) (y String))
    (=> (and (inv n vi)
             (= vi (str.++ x "BW" y))
             (= vo (str.++ x "W" y)))
        (inv (+ n 1) vo))))
(assert
  (forall ((n Int) (vi String) (vo String) (x String) (y String))
    (=> (and (inv n vi)
             (= vi (str.++ x "WB" y))
             (= vo (str.++ x "W" y)))
        (inv (+ n 1) vo))))
(assert (forall ((n Int)) (=> (inv n "B") false)))
(check-sat)
