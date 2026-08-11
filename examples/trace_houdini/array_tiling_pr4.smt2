; Array-tiling loop over 4 interleaved value stores per iteration.
;
; Performance regression fixture, not (yet) a proof-goal benchmark: before
; the max_terms_per_relation cap on mutate_candidates() (see
; DEFAULT_MAX_MUTATION_TERMS_PER_RELATION in seedminer.py),
; --trace-houdini --mut took on the order of 30+ minutes on this file. The
; combined seed-plus-trace candidate pool for `inv` here runs to ~130
; numeric equalities/inequalities; uncapped pairwise --mut combination over
; that pool produces tens of thousands of derived candidates, each of which
; MultiHoudini must then individually verify against this program's
; Store/ite-heavy array rules -- inherently expensive per-check. See
; tests/test_trace_houdini.py::test_trace_houdini_mut_bounds_large_pools.
;
;here '4*CC' is 'CELLCOUNT' of original program

(declare-var CC Int)
(declare-var i Int)
(declare-var i1 Int)
(declare-var a (Array Int Int))
(declare-var a1 (Array Int Int))
(declare-var a2 (Array Int Int))
(declare-var a3 (Array Int Int))
(declare-var a4 (Array Int Int))
(declare-var val1 Int)
(declare-var val2 Int)
(declare-var val3 Int)
(declare-var val4 Int)
(declare-var minval Int)

(declare-rel inv ((Array Int Int) Int Int Int Int Int Int Int))
(declare-rel fail ())

(rule (=> (and (> CC 0) (= val1 1) (=  val2 3) (= val3 7) (=  val4 5) (= i 1))
          (inv a i CC val1 val2 val3 val4 minval)))

(rule (=> (and
           (inv a i CC val1 val2 val3 val4 minval)
           (<= i (* 1 CC))
           (= i1 (+ i 1))
           (= a1 (ite (<= minval val4)
		      (store a (- (* 4 i) 4) val4)
		      (store a (- (* 4 i) 4) 0)))
           (= a2 (ite (<= minval val3)
		      (store a1 (- (* 4 i) 3) val3)
		      (store a1 (- (* 4 i) 3) 0)))
           (= a3 (ite (<= minval val2)
		      (store a2 (- (* 4 i) 2) val2)
		      (store a2 (- (* 4 i) 2) 0)))
           (= a4 (ite (<= minval val1)
		      (store a3 (- (* 4 i) 1) val1)
		      (store a3 (- (* 4 i) 1) 0))))
          (inv a4 i1 CC val1 val2 val3 val4 minval)))

(rule (=> (and
           (inv a i CC val1 val2 val3 val4 minval)
           (not (<= i (* 1 CC)))
           (<= 0 i1)
           (< i1 (* 4 CC))
           (not (or (<= minval (select a i1)) (= (select a i1) 0))))
          fail))

(query fail)
