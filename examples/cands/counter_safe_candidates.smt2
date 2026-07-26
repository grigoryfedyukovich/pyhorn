; User-supplied candidate file for ../seed_houdini/counter_safe.smt2.
;
; That benchmark is:
;   x := 0
;   while (x < 10) { x := x + 1 }
;   assert x <= 10
;
; Run with:
;   chc-bounded-explorer ../seed_houdini/counter_safe.smt2 \
;     --cands counter_safe_candidates.smt2 --print-invariants
;
; or combined with seed mining (user candidates are merged with mined ones):
;   chc-bounded-explorer ../seed_houdini/counter_safe.smt2 \
;     --seed-houdini --cands counter_safe_candidates.smt2 --print-invariants
;
; Format notes
; ------------
; - One or more define-fun commands per uninterpreted, non-query predicate
;   of the target CHC file (query/error relations such as `fail` never take
;   candidates and are silently ignored if named here).
; - The number of parameters must match the predicate's declared arity; the
;   parameter *names* are free -- they are bound to the predicate's own
;   canonical variables purely by position, not by spelling.
; - A conjunction in the body is automatically split into separate Houdini
;   candidates, so a single define-fun can carry several independent guesses
;   at once.
; - declare-fun/declare-rel/set-logic/comments are accepted for readability
;   and are otherwise ignored.

; `x >= -100` is a deliberately loose (but true) lower bound: Houdini has
; nothing to remove it for, so it survives filtering as extra evidence that
; nothing here needed to be exactly the tightest possible invariant.
;
; `x <= 10` is the fact that actually makes the query clause valid.
(define-fun inv ((x Int)) Bool
  (and (>= x -100)
       (<= x 10)))
