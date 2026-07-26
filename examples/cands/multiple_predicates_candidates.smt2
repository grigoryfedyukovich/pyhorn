; User-supplied candidate file for ../seed_houdini/multiple_predicates.smt2.
;
; That benchmark is:
;   p(0)
;   p(x) => q(x)
;   q(x) & x < 3 => q(x+1)
;   q(x) & x > 3 => fail
;
; Two predicates, `p` and `q`, each get their own define-fun. `q`'s body
; below also includes one deliberately wrong guess (`x = 999`) to
; demonstrate that MultiHoudini removes exactly the conjuncts that are not
; inductive and still reports Success on what remains.
;
; Run with:
;   chc-bounded-explorer ../seed_houdini/multiple_predicates.smt2 \
;     --cands multiple_predicates_candidates.smt2 \
;     --print-invariants --debug

(declare-rel p (Int))
(declare-rel q (Int))

(define-fun p ((x Int)) Bool
  (= x 0))

(define-fun q ((x Int)) Bool
  (and (>= x 0)
       (<= x 3)
       (= x 999)))
