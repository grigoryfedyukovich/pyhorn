; Harder, syntactically distinct rewrite of the old shared multiphase transfer.
; Three phases (fill / hold / drain) now share a length invariant; an extra
; "tag" String is threaded through all phases and must stay equal to the
; original fill content (relational word-equation style). Length is still
; tracked by an Int, but the hold phase performs a no-op that can only be
; proved inductive once both the length equality and the tag equality are
; retained together. Forces multi-predicate candidate propagation across a
; longer chain than the original two-phase version.
;
; Expected: safe. Known invariants (all three predicates):
;   str.len(s) = n
;   tag = original content snapshot
(set-logic HORN)
(declare-fun fill  (String Int String) Bool)
(declare-fun hold  (String Int String) Bool)
(declare-fun drain (String Int String) Bool)

; begin with empty buffer, zero count, empty tag
(assert (fill "" 0 ""))

; fill phase: append and grow count; tag records the growing content
(assert
  (forall ((s String) (n Int) (tag String))
    (=> (and (fill s n tag) (< n 4))
        (fill (str.++ s "x") (+ n 1) (str.++ tag "x")))))

; transition fill -> hold once full
(assert
  (forall ((s String) (n Int) (tag String))
    (=> (and (fill s n tag) (= n 4))
        (hold s n tag))))

; hold phase: pure stutter (tests that both equalities survive a no-op step)
(assert
  (forall ((s String) (n Int) (tag String))
    (=> (hold s n tag)
        (hold s n tag))))

; transition hold -> drain
(assert
  (forall ((s String) (n Int) (tag String))
    (=> (hold s n tag)
        (drain s n tag))))

; drain phase: peel one character, decrement count; tag must stay unchanged
(assert
  (forall ((s String) (n Int) (tag String))
    (=> (and (drain s n tag) (> n 0))
        (drain (str.substr s 1 (- (str.len s) 1)) (- n 1) tag))))

; safety on every phase
(assert
  (forall ((s String) (n Int) (tag String))
    (=> (and (fill s n tag)
             (or (not (= (str.len s) n))
                 (not (= s tag))))
        false)))
(assert
  (forall ((s String) (n Int) (tag String))
    (=> (and (hold s n tag)
             (or (not (= (str.len s) n))
                 (not (= s tag))))
        false)))
(assert
  (forall ((s String) (n Int) (tag String))
    (=> (and (drain s n tag)
             (or (not (= (str.len s) n))
                 (and (> n 0) (not (str.prefixof s tag)))))
        false)))

(check-sat)
