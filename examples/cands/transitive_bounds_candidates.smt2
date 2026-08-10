; User-supplied candidates for ../seed_houdini/transitive_bounds_safe.smt2.
; Deliberately supplies only the two inequality "legs" -- x<=y and y<=z --
; not x<=z itself, which is the file's actual safety property. With --mut,
; MultiHoudini also gets x<=z (derived via inequality-transitivity chaining:
; x<=y and y<=z give x<=z) as an independently-retained candidate in its own
; right, not just as something Z3's certification-time arithmetic happens to
; combine on the fly.
;
; Run with:
;   pyhorn-expl --cands transitive_bounds_candidates.smt2 --mut \
;     --debug --print-invariants \
;     ../seed_houdini/transitive_bounds_safe.smt2
(define-fun inv ((x Int) (y Int) (z Int)) Bool
  (and (<= x y) (<= y z)))
