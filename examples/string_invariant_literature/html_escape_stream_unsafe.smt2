; Buggy sanitizer: '<' is copied unchanged, so input "<" reaches a bad output.
(declare-fun inv (String String) Bool)
(assert (forall ((input String)) (inv input "")))
(assert
  (forall ((rem String) (out String))
    (=> (and (inv rem out)
             (> (str.len rem) 0)
             (= (str.at rem 0) "<"))
        (inv (str.substr rem 1 (- (str.len rem) 1))
             (str.++ out "<")))))
(assert
  (forall ((rem String) (out String))
    (=> (and (inv rem out)
             (> (str.len rem) 0)
             (not (= (str.at rem 0) "<")))
        (inv (str.substr rem 1 (- (str.len rem) 1))
             (str.++ out (str.at rem 0))))))
(assert
  (forall ((rem String) (out String))
    (=> (and (inv rem out) (str.contains out "<")) false)))
(check-sat)
