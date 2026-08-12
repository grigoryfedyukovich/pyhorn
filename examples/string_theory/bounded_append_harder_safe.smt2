; Harder, syntactically distinct rewrite of the old shared bounded_append_safe.
; Capacity is now an explicit Int parameter; two buffers (primary + overflow
; shadow) must stay consistent; guard is a relational length check rather
; than a constant. Requires the inductive fact
;   str.len(buf) + str.len(shadow) <= capacity
; together with the per-buffer bounds. SeedMiner still finds the pieces, but
; MultiHoudini must retain the relational combination across the step that
; grows only one buffer.
;
; Expected: safe. Known invariant family:
;   0 <= str.len(buf) <= capacity
;   0 <= str.len(shadow) <= capacity
;   str.len(buf) + str.len(shadow) <= capacity
(set-logic HORN)
(declare-fun inv (String String Int) Bool)

; start empty under a non-trivial capacity
(assert
  (forall ((cap Int))
    (=> (>= cap 5)
        (inv "" "" cap))))

; grow primary while total occupancy stays strictly below capacity
(assert
  (forall ((buf String) (shadow String) (cap Int))
    (=> (and (inv buf shadow cap)
             (< (+ (str.len buf) (str.len shadow)) cap)
             (< (str.len buf) cap))
        (inv (str.++ buf "A") shadow cap))))

; grow shadow under the same relational guard
(assert
  (forall ((buf String) (shadow String) (cap Int))
    (=> (and (inv buf shadow cap)
             (< (+ (str.len buf) (str.len shadow)) cap)
             (< (str.len shadow) cap))
        (inv buf (str.++ shadow "B") cap))))

; safety: neither buffer nor their sum may exceed capacity
(assert
  (forall ((buf String) (shadow String) (cap Int))
    (=> (and (inv buf shadow cap)
             (or (> (str.len buf) cap)
                 (> (str.len shadow) cap)
                 (> (+ (str.len buf) (str.len shadow)) cap)))
        false)))

(check-sat)
