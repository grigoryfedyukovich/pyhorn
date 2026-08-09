# `(set-logic HORN)` and String don't mix in this version of Z3

**Status:** fixed across the example corpus.

## The problem

```
$ z3 examples/string_invariant_literature/regex_alphabet_closure_safe.smt2
(error "line 3 column 18: Parsing function declaration. Expecting sort
list '(': unknown sort 'String'")
```

`(set-logic HORN)` followed by any use of the `String` (or `RegLan`) sort
breaks parsing under Z3's own standalone command-line `set-logic`
enforcement: the declared logic doesn't include String theory, so every
later `String`-sorted declaration is rejected as an unknown sort. This was
first found by hand in one example file
(`examples/string_theory/helper_lemma_safe.smt2`, written in this round of
work) and fixed there and in four sibling files by simply omitting the
line. It was found *again*, independently, in
`render_candidate_verification_smt2`'s dumped output (see
`docs/candidate_validation_theory_coverage.md`, bug 2) and fixed there by
conditionally omitting the line. Both of those fixes were narrowly scoped
at the time.

This doc is the result of going back and checking how far the same problem
actually reaches, prompted by a person testing one of the example files
directly against the real `z3` binary (not just through this tool's own
Python-API-based parsing, which tolerates the combination -- see below)
and hitting exactly this error.

## Scope

Every `.smt2` file under `examples/` that has both `(set-logic HORN)` and
a `String`/`RegLan` sort was affected -- **30 files**, spanning
`examples/string_theory/`, `examples/string_invariant_literature/`, and
`examples/mixed_theories/coffee_can_step_counter_safe.smt2`. This covered
both syntax dialects equally (Z3 Datalog-style `declare-rel`/`rule`/`query`
*and* pure SMT-LIB2 `declare-fun`/`assert`/`forall`) -- dialect was never
actually the deciding factor, String was.

One pre-existing file,
`examples/string_theory/fixedpoint_regex_safe.smt2`, never had the line
and served as a working reference confirming that omitting it is both
sufficient and already an established (if inconsistently applied)
convention in this codebase.

## Why this didn't break `pytest`

Every one of the 30 files parses and behaves correctly through this
tool's own pipeline (`parse_chc_file`, `z3.parse_smt2_string` /
`z3.Fixedpoint().parse_string()` via the Python API) -- that's why 282
tests were passing throughout this whole round of fixes despite the bug
being present in 30 example files the entire time. The break is specific
to Z3's standalone command-line SMT-LIB2 conformance checking, which
enforces the declared logic's sort restrictions strictly; the Python API
does not restrict sorts the same way regardless of what `set-logic` says.
Nothing here was caught by this tool's own test suite -- only by
independently trying to run a file with plain `z3`.

## Why it matters anyway

These files are documented throughout the README as benchmarks meant to
be portable -- "hand this file to any HORN-capable solver" is the explicit
framing for `--dump-promising-candidates`' output, and the example
corpus generally serves the same purpose. A benchmark file that the most
obvious tool for opening it (the actual `z3` binary) refuses to parse is
a real usability defect, independent of whether this tool's own pipeline
happens to route around it.

## Fix

`(set-logic HORN)` removed from all 30 files; nothing else changed. No
test in this repository asserts on the literal presence of that line in
any of these files (checked directly before editing), so this could not
regress the existing suite. The four files ported from
pyhorn-bounded-explorer 0.0.15 in this round had their header comments
softened from "ported verbatim" to "ported from," since they're no longer
byte-identical to the source.

If you're auditing this yourself: `grep -rl "set-logic HORN" examples/ |
xargs grep -lE '\bString\b|\bRegLan\b'` should now return nothing.
