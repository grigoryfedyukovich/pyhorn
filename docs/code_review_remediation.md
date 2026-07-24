# v0.0.10 code-review remediation

This release addresses the findings in `pyhorn_code_review.md`.

| Review item | Resolution |
|---|---|
| BUG-1 | Replaced load-bearing `assert` statements with explicit runtime checks. |
| BUG-2 / SMELL-6 | Internal Z3 expression/declaration maps now use AST IDs. |
| BUG-3 | `SeedMiner.mine()` resets state and is idempotent. |
| BUG-4 | Canonical-variable allocation returns an updated copy of the name set. |
| BUG-5 | Acyclic topological traversal uses `deque.popleft()`. |
| BUG-6 / PERF-3 | Exact repeated SAT traces reuse a cached model without rechecking. |
| SMELL-1 | Parsing uses the already-read text with `Fixedpoint.parse_string()`. |
| SMELL-2 | Relation discovery uses one command-parser pass. |
| SMELL-3 | CLI no longer catches arbitrary `ValueError`. |
| SMELL-4 | Common SMT symbols are quoted directly without allocating Z3 constants. |
| SMELL-5 | Pre-1.0 constructor and CLI aliases were removed. |
| SMELL-7 / PERF-5 | Predicate-locality free-variable results are cached safely. |
| SMELL-8 | Per-depth statistics have one append path. |
| SMELL-9 | Debug reporting uses one block. |
| SMELL-10 | `pyhorn_bnd.__version__` is exported. |
| PERF-1 | Trace paths use linked nodes; tuples are created only for yielded traces. |
| PERF-2 | Solver contexts are indexed by first rule before LCP comparison. |
| PERF-4 | SSA step/state caches are bounded LRU caches with configurable limits. |
| PERF-6 | Direct argument deduplication uses AST IDs. |
| PERF-7 | Houdini candidate maps are sorted once. |
| PERF-8 | Program symbol names are collected during normalized-program construction. |

The regression suite contains focused tests for the high-risk fixes, including
optimized-mode safety, parser behavior, exact-prefix reuse, cache eviction, and
SeedMiner idempotence.
