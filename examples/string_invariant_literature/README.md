# Literature-derived string invariant benchmarks

This directory contains compact linear-CHC encodings of representative string
invariant problems from regular model checking, string rewriting, and static
analysis of string-manipulating loops.

The benchmark files are intentionally small enough for parser and regression
tests, but several require genuinely non-local regular-language invariants.
They are not all expected to be solved by the current syntactic SeedMiner.

| File | Class | Current intended use |
|---|---|---|
| `hornstr_token_pass_safe.smt2` | HornStr token-passing RMC example | regular invariant synthesis |
| `hornstr_mu_puzzle_safe.smt2` | MU string-rewrite system | modular/automata invariant synthesis |
| `hornstr_mu_puzzle_unsafe_miu.smt2` | reachable MU variant | bounded counterexample regression |
| `coffee_can_odd_white_safe.smt2` | Gries coffee-can rewriting | parity/automata invariant synthesis |
| `single_token_line_safe.smt2` | parameterized token movement | regular invariant synthesis |
| `regex_alphabet_closure_safe.smt2` | regex closure | SeedMiner + MultiHoudini |
| `html_escape_stream_safe.smt2` | streaming sanitizer | SeedMiner + MultiHoudini |
| `html_escape_stream_unsafe.smt2` | buggy sanitizer | bounded counterexample regression |
| `copy_decomposition_safe.smt2` | character-by-character copy | relational word-equation invariant |
| `replace_sanitize_safe.smt2` | streaming `str.replace` sanitizer | SeedMiner + MultiHoudini |
| `prefix_closure_safe.smt2` | prefix-closed language fragment | SeedMiner + MultiHoudini |
| `short_word_unsafe.smt2` | minimal word-rewrite bug | bounded counterexample regression |

The two HornStr examples are manually re-encoded from Examples 1 and 2 of:

- H. Jiang, A. W. Lin, O. Markgraf, P. Rümmer, D. Stan,
  *HornStr: Invariant Synthesis for Regular Model Checking as Constrained Horn
  Clauses*, CAV 2025, arXiv:2505.15959.
- Artifact: <https://doi.org/10.5281/zenodo.15153023> (Apache-2.0).

The sanitizer and copy examples are original PyHorn encodings inspired by the
program-analysis applications surveyed in:

- R. Amadini, G. Gange, P. Stuckey, *A Survey on String Constraint Solving*,
  ACM Computing Surveys 2021, arXiv:2002.02376.

See `docs/string_invariant_literature.md` for known invariants, current results,
and a synthesis roadmap.
