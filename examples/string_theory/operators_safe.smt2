; Representative SMT-LIB String operators in a finite acyclic CHC.
(declare-var s String)
(declare-rel inv (String))
(declare-rel fail ())

(rule (inv "abc123"))
(rule
  (=> (and (inv s)
           (not
             (and (= (str.len s) 6)
                  (str.prefixof "abc" s)
                  (str.suffixof "123" s)
                  (str.contains s "c1")
                  (= (str.at s 0) "a")
                  (= (str.substr s 1 2) "bc")
                  (= (str.indexof s "12" 0) 3)
                  (= (str.replace s "abc" "x") "x123")
                  (= (str.to_int (str.substr s 3 3)) 123)
                  (str.contains s (str.from_int (str.indexof s "1" 0))))))
      fail))
(query fail)
