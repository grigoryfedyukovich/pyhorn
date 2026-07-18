# `bench_horn` parser coverage

## Corpus snapshot

The parser was checked against the complete uploaded `bench_horn` directory:

- **352** SMT-LIB files;
- **1,056** `rule` commands;
- **704** `declare-rel` commands;
- **2,328** `declare-var` commands;
- **4** `define-fun` commands;
- **352** `query` commands, including **170** queries carrying
  `:print-certificate true`.

All 352 files parse successfully with `parse_chc_file(...,
slice_program=False)`.

This is currently a **parser and normalization guarantee**, not a claim that
bounded exploration terminates quickly or proves every benchmark.

## CHC organization

Every file in this corpus has the same high-level linear shape after
normalization:

1. one ENTRY fact;
2. one self-loop transition over the state relation;
3. one transition from the state relation to a nullary error relation.

For every file, the normalized program contains:

- exactly 3 rules;
- exactly 2 relations;
- exactly 1 fact rule;
- exactly 1 inductive/self-loop rule;
- exactly 1 query rule;
- a nullary query relation;
- source and destination arguments whose Z3 sorts match the corresponding
  relation signature.

The state relation is usually named `inv`, but the corpus also uses names such
as `itp`, `inv1`, `itp1`, and `FUN`.  The error relation is normally `fail`,
with two files using `err`.

## Sort coverage

| File category | Files |
|---|---:|
| Integer-only declarations | 219 |
| Integer and `(Array Int Int)` declarations | 117 |
| Mixed `Int` and `Bool` declarations | 12 |
| Boolean-only declarations | 4 |

No file declares a `Real` relation argument.  One benchmark nevertheless uses
SMT-LIB `/` over integer terms; Z3 normalizes that expression by inserting
`to_real` coercions.

## Operator coverage

The following counts record how many source files contain each operator after
comments are removed and SMT-LIB commands are tokenized.

| Operator or construct | Files |
|---|---:|
| `and` | 352 |
| `=` | 351 |
| `not` | 330 |
| `+` | 326 |
| `<` | 202 |
| `>=` | 197 |
| `ite` | 180 |
| `-` | 143 |
| `>` | 129 |
| `select` | 117 |
| `store` | 110 |
| `<=` | 106 |
| `*` | 84 |
| `or` | 52 |
| `mod` | 51 |
| `div` | 14 |
| `define-fun` | 4 |
| constant-array syntax `(as const ...)` | 3 |
| `/` | 1 |
| `distinct` | 1 |

The fixedpoint frontend expands `define-fun` applications and may simplify
surface syntax.  For example, `distinct` over two integer terms is normalized
to a negated equality.

## Extracted examples

Ten small files from the corpus are checked into `examples/bench_horn/`:

- integer state and non-variable relation arguments;
- Boolean-only state;
- mixed Boolean/integer state with `ite` and `mod`;
- array `select` and `store`;
- constant arrays and multiple array arguments;
- integer `div` and `mod`;
- nonlinear multiplication;
- `define-fun`, `or`, and `ite`;
- `distinct` and unary negation;
- `/` over integer terms with Real coercion.

The default test suite parses these files and checks their normalized relation
signatures, rule shape, argument sorts, and expected Z3 operator kinds.

## Reproducing the full-corpus check

Run the standalone checker:

```bash
PYTHONPATH=src python3 tools/check_chc_corpus.py \
  /path/to/bench_horn \
  --manifest tests/data/bench_horn_manifest.txt
```

Or run the external pytest regression:

```bash
PYHORN_BENCH_HORN_DIR=/path/to/bench_horn \
  python3 -m pytest -q tests/test_bench_horn_corpus.py
```

The manifest records the 352 filenames in the scanned corpus.  Additional
`.smt2` files are also parsed; the manifest only ensures that none of the known
files are missing.
