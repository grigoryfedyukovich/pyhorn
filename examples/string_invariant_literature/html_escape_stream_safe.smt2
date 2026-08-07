; Streaming HTML-angle-bracket escaping, inspired by sanitizer analyses.
; The first state component is the unprocessed suffix and the second is output.
(set-logic HORN)
(declare-fun inv (String String) Bool)

(assert (forall ((input String)) (inv input "")))

(assert
  (forall ((rem String) (out String))
    (=> (and (inv rem out)
             (> (str.len rem) 0)
             (= (str.at rem 0) "<"))
        (inv (str.substr rem 1 (- (str.len rem) 1))
             (str.++ out "&lt;")))))

(assert
  (forall ((rem String) (out String))
    (=> (and (inv rem out)
             (> (str.len rem) 0)
             (= (str.at rem 0) ">"))
        (inv (str.substr rem 1 (- (str.len rem) 1))
             (str.++ out "&gt;")))))

(assert
  (forall ((rem String) (out String))
    (=> (and (inv rem out)
             (> (str.len rem) 0)
             (not (= (str.at rem 0) "<"))
             (not (= (str.at rem 0) ">")))
        (inv (str.substr rem 1 (- (str.len rem) 1))
             (str.++ out (str.at rem 0))))))

(assert
  (forall ((rem String) (out String))
    (=> (and (inv rem out)
             (or (str.contains out "<")
                 (str.contains out ">")))
        false)))
(check-sat)
