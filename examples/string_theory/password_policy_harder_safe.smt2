; Harder, syntactically distinct rewrite of the old shared password_policy.
; Construction now interleaves three character classes under an explicit
; Int length counter; the final policy requires
;   - length in [6,10]
;   - at least one lower, one digit, one upper (encoded via three regex
;     witnesses that must all hold simultaneously)
;   - the ghost length counter stays exact.
; The inductive invariant therefore mixes a numeric equality with three
; independent regular-language membership facts; SeedMiner must keep all
; four candidates for MultiHoudini to succeed.
;
; Expected: safe.
(set-logic HORN)
(declare-fun inv (String Int) Bool)

(define-fun lower () RegLan (re.range "a" "z"))
(define-fun digit () RegLan (re.range "0" "9"))
(define-fun upper () RegLan (re.range "A" "Z"))
(define-fun alnum () RegLan
  (re.union lower (re.union digit upper)))

; seed that already satisfies the three-class requirement
(assert (inv "a0Axxx" 6))

; three constructors, each preserving the ghost length
(assert
  (forall ((s String) (n Int))
    (=> (and (inv s n) (< n 10))
        (inv (str.++ s "b") (+ n 1)))))
(assert
  (forall ((s String) (n Int))
    (=> (and (inv s n) (< n 10))
        (inv (str.++ s "7") (+ n 1)))))
(assert
  (forall ((s String) (n Int))
    (=> (and (inv s n) (< n 10))
        (inv (str.++ s "Z") (+ n 1)))))

; policy: length window + exact ghost + presence of each class
(assert
  (forall ((s String) (n Int))
    (=> (and (inv s n)
             (or (< n 6)
                 (> n 10)
                 (not (= (str.len s) n))
                 (not (str.in_re s (re.* alnum)))
                 (not (str.in_re s (re.++ (re.* alnum) lower (re.* alnum))))
                 (not (str.in_re s (re.++ (re.* alnum) digit (re.* alnum))))
                 (not (str.in_re s (re.++ (re.* alnum) upper (re.* alnum))))))
        false)))

(check-sat)
