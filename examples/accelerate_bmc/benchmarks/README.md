# `--accelerate-bmc` benchmark suite

20 CHC instances, each unsafe (reaches `fail`), each requiring somewhere
between ~300 million and ~15 billion real loop iterations to reach the
counterexample. Plain unrolling needs a `--upto` at least that large --
not shown running to completion below, because it wouldn't finish in any
reasonable time (see the small-scale figures for what "wouldn't finish"
extrapolates from). `--accelerate-bmc` finds every one of them at search
depth 3-7, in well under a second each, regardless of how large the
threshold is.

Verified two ways for every design: (1) a small-scale twin (thresholds in
the tens) where *both* plain and accelerated search are fast enough to
run to completion, confirming plain BMC's depth genuinely scales with the
threshold while accelerated search's doesn't; (2) the large-scale file
below, run only with `--accelerate-bmc`, confirming the search depth is
identical to the small-scale run despite thresholds up to nine orders of
magnitude larger. All 20 were also run end-to-end through the actual
`bounded_explorer.py --accelerate-bmc --json` CLI, not just internal
calls.

| # | File | Pattern | Threshold (large) | Accel depth | Plain depth (small twin, thresh. in `()`) |
|---|------|---------|--------------------:|:-----------:|---|
| 01 | up_counter_unit | single counter, unit step | 1,000,000,000 | 3 | 52 (50) |
| 02 | down_counter_unit | single counter, counts down | 1,000,000,000 | 3 | 52 (50) |
| 03 | up_counter_step13 | non-unit step (13); regression case for an off-by-one bug found while building this suite | 1,000,000,000 | 3 | 41 (500) |
| 04 | two_var_lockstep | two variables advancing at different rates in one branch | 500,000,000 | 3 | 42 (40) |
| 05 | three_var_lockstep | three variables, three different rates | 300,000,000 | 3 | 42 (40) |
| 06 | up_counter_negative_init | counts up from a large negative start | 500,000,000 | 3 | 82 (40) |
| 07 | down_counter_step | counts down with a non-unit step (17) | 1,000,000,000 | 3 | 32 (500) |
| 08 | up_counter_inclusive_guard | non-strict (`<=`) loop guard; regression case for the same off-by-one bug as #03 | 1,000,000,000 | 3 | 53 (50) |
| 09 | two_var_converging | guard compares two *variables* to each other, not a variable to a constant | 800,000,000 | 3 | 32 (60) |
| 10 | up_counter_conjunctive_guard | compound guard mixing a real (monotonic) condition with an always-true one; regression case for a second, distinct "wrong direction" bug found in this suite's construction | 1,000,000,000 | 3 | 52 (50) |
| 11 | two_phase_classic | two sequential phases, hand-off between two different variables | 900,000,000 | 4 | 72 (45) |
| 12 | two_phase_payload_both_phases | one payload variable moves in both phases at different rates | 900,000,000 | 4 | 47 (45) |
| 13 | two_phase_decrement_then_hold | phase 1 counts down, phase 2 holds and grows a payload | 900,000,000 | 4 | 72 (45) |
| 14 | two_phase_fast_second_phase | second phase advances 1000x faster than the first | 999,000,000 | 4 | 28 (30) |
| 15 | two_phase_three_vars | three variables split across two phases | 900,000,000 | 4 | 72 (45) |
| 16 | two_phase_inclusive_guards | two-phase version of the `<=` guard case (#08) | 900,000,000 | 4 | 74 (45) |
| 17 | three_phase_relay | three sequential phases, one payload variable per phase | 900,000,000 | 5 | 77 (45) |
| 18 | four_phase_relay | four sequential phases | 900,000,000 | 6 | 86 (48) |
| 19 | five_phase_relay | five sequential phases; also the regression case for a guard-simplification bug (a vacuously-true residual that silently broke one branch in five-way nested `ite`s) | 900,000,000 | 7 | 92 (50) |
| 20 | three_phase_relay_variable_rates | three phases, three different rates (1, 1000, 7) on one payload variable | 400,000,000,000 | 5 | 45 (15,100) |

## Reproducing

```bash
python3 bounded_explorer.py --accelerate-bmc --debug 01_up_counter_unit.smt2
```

Every file resolves to `Counterexample of length <accel depth> found` in
well under a second. To see the contrast, run any of them *without*
`--accelerate-bmc` -- expect it to still be running well past the point
of usefulness, which is the point.
