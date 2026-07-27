# grip JSON benchmark

grip measured against other parser-combinator libraries on one fixed task, plus a
hand-written scanner (the runtime floor) and two different-model references.

## Task

Strict RFC-8259 validate and count leaf scalars, no DOM. Every parser rejects malformed
numbers (`00`, `1.`, `1e`), bad string escapes, unescaped control bytes, and trailing
garbage, then returns a leaf count: number / string / keyword = 1, object keys not
counted, containers sum their children. The shared spec each harness implements is
`bench/cross-lang/TASK.md`. Every same-task row returns the identical count — that is the
correctness gate:

| file                | bytes  | leaves | character |
|---------------------|-------:|-------:|-----------|
| `canada.json`       | 2.1 MB | 111130 | ~99% numbers |
| `citm_catalog.json` | 1.6 MB |  16390 | objects, keys, nesting |
| `twitter.json`      | 616 KB |  11600 | strings, Unicode, escapes |

## Method

Best-of-20, input preloaded into memory, timing excludes I/O, a barrier (`@[noinline]` /
`black_box` / `Sys.opaque_identity` / an `IO.Ref` sink) prevents the compiler eliding the
parse. The Lean rows are timed in-process by `bench/Bench.lean` (prim-parser by its own
harness, same technique); each cross-language harness times itself. Numbers are one
session.

Machine: Apple Silicon (arm64-darwin), Darwin 25.2. Every toolchain is native arm64: Lean
v4.28.0, Rust 1.95, OCaml 5.3.0, GHC 9.14.1 (arm64 Homebrew — the Haskell rows are not
emulated).

Cross-runtime rows are context, not a controlled comparison: garbage collection, reference
counting, and value boxing differ per runtime. The controlled comparison is the Lean set.

## Same-task results (ms, lower is better)

Each row is a strict validator, non-allocating (no per-element list or `Vec`), bulk-scans
string bodies, and returns the leaf counts above. Sorted by `canada`.

| parser                                  | canada | citm  | twitter | runtime      |
|-----------------------------------------|-------:|------:|--------:|--------------|
| nom (Rust)                              |   1.70 |  1.24 |    0.49 | rustc 1.95   |
| hand-written scanner (Lean, no combinators) | 5.12 | 2.93 | 1.23 | Lean v4.28.0 |
| megaparsec (Haskell)                    |   9.86 |  4.45 |    1.72 | GHC 9.14.1   |
| attoparsec (Haskell)                    |  12.76 |  5.07 |    2.01 | GHC 9.14.1   |
| **grip** (Lean)                         |  19.38 |  7.73 |    2.88 | Lean v4.28.0 |
| Std.Internal.Parsec (Lean)              |  21.34 | 11.17 |    4.89 | Lean v4.28.0 |
| angstrom (OCaml)                        |  39.04 | 12.56 |    3.79 | OCaml 5.3.0  |
| prim-parser byte port (deep `G`, local) |  71.01 | 32.29 |   10.89 | Lean v4.28.0 |

**Two things are labeled prim-parser; do not confuse them.** The row above is a byte-level
deep-embedded reimplementation (the sibling `research/prim-parser` `G` framework, a reified
combinator GADT interpreted at run time). The actual upstream prim-parser
(`janmasrovira/prim-parser` main `e1f3f7b`, char-level `List.Vector Char n`) was measured
separately, count-only, same task: **~698 ms on canada, ~35x slower than grip** — its char
linked-list input (no O(1) access, no bulk scan) is the cost. The byte port (71 ms)
isolates the shallow-vs-deep axis; the upstream (698 ms) shows the char-vs-byte axis.

Versions: attoparsec 0.14.4, megaparsec 9.8.1, nom 7.1.3, angstrom 0.16.1. Each uses its
own library's idiomatic combinators; none builds a DOM.

## Reading the numbers

**Lean, same toolchain (the controlled set).** grip is the fastest combinator parser in
Lean. It beats `Std.Internal.Parsec` on every file (~1.1x canada, ~1.45x citm, ~1.7x
twitter — first-byte `dispatch` and the single-pass `stringLit` scanner), and it is ~35x
faster than upstream prim-parser. The byte port isolates why: it is a deep-embedded,
reified GADT interpreted at run time, while grip is a shallow embedding (each combinator a
direct function over `ByteArray → Nat → ParseResult`), and grip beats even that port by
~3.6x. So the ~35x decomposes as ~10x char-vs-byte plus ~3.6x shallow-vs-deep. grip sits
~3.8x above the hand-written Lean floor (5.12 ms) — the combinator overhead over raw byte
recursion in the same runtime.

**Cross-language.** Both mature Haskell libraries beat grip on native arm64: megaparsec
(9.86) and attoparsec (12.76). angstrom (39.0) is slower than grip even after removing its
per-array list allocation and switching to bulk string scanning — per-combinator overhead
dominates. Strict-eval native FP does not by itself make a combinator library fast. nom is
~11x grip and leads every file; that gap is the systems-language runtime (borrowed slices,
no boxing, no RC), not the combinator model.

**What grip offers.** The fastest combinator parser in Lean, and the only one here with a
static grade on every parser, a machine-checked soundness proof, and a kernel-total `fix`.

## Different model / task (context only)

| parser                    | canada | citm | twitter | note                                             |
|---------------------------|-------:|-----:|--------:|--------------------------------------------------|
| lean4-parser (Lean, char) | 103.0  | 66.7 |   17.9  | `Char`-level (decodes UTF-8 per token); its byte mode is broken on v4.28.0 (fixed only in v4.32) |
| Lean.Json (Lean, DOM)     |  69.4  |  5.7 |    4.0  | builds a full `Lean.Json` tree — strictly more work than validate-and-count |

## Fairness

Every same-task harness: (1) validates the RFC grammar; (2) is non-allocating — no
`sepBy`-style throwaway container per array; (3) bulk-scans safe string runs then branches
on escapes; (4) returns the identical counts; (5) uses the library's own combinators, not
a hand-rolled scanner. Four issues were fixed while assembling this table:

- angstrom's `sep_by1` built an int list per array → non-allocating fold.
- the attoparsec / megaparsec string bodies validated byte-by-byte → bulk `takeWhile` +
  escape branch.
- the Haskell rows were first measured under Rosetta → re-measured on native arm64 GHC.
- the prim-parser harness was first a hand-written byte scanner touching prim-parser only
  for whitespace → rewritten as a real `G`-framework combinator parser. That correction
  moved prim-parser from a spurious 8 ms to its true 71 ms.

## Reproduce

```
lake exe bench                                     # Lean rows (grip, Std.Parsec, hand, Lean.Json)
cd bench/cross-lang/nom         && cargo run --release -- <file>
cd bench/cross-lang/atto        && cabal run atto-bench -- <file>
cd bench/cross-lang/megaparsec  && cabal run megaparsec-bench -- <file>
cd bench/cross-lang/angstrom    && dune exec ./main.exe -- <file>
cd bench/cross-lang/lean4-parser && lake build && .lake/build/bin/L4pBench <file>
cd bench/cross-lang/prim-parser && lake exe cache get && lake build && .lake/build/bin/gripjson <file>
```

`<file>` is one of `bench/data/{canada.json,citm_catalog.json,twitter.json}`. The
prim-parser harness path-requires the sibling `research/prim-parser` repo and pulls mathlib
from the prebuilt cache. On arm64 macOS install native GHC with `brew install ghc
cabal-install` so the Haskell rows are not run under Rosetta.

## Where grip's time goes

The same parse, several ways, on canada.json (all count 111130):

| approach                                   | canada ms | note                                          |
|--------------------------------------------|----------:|-----------------------------------------------|
| nom (Rust)                                 |     ~1.7  | borrowed slices, no boxing, no RC             |
| hand-written Lean scanner (no combinators) |     ~5.1  | the Lean runtime floor                        |
| **grip today**                             |    ~19    | combinators; scan loops specialized, single-pass string scanner |
| grip before `@[specialize]` scan loops     |    ~34    | per-byte predicate called indirectly          |
| grip before single-constructor result      |    ~40    | two heap objects per step (`Except` + `Prod`) |
| prim-parser (deep-embedded `G`)            |    ~71    | reified combinator GADT interpreted at run time |

grip's own optimization history (grade algebra unchanged throughout):

- **Single-constructor result** (`Except Err (α × Nat)` to `ParseResult α`): one heap
  object per success, not two. ~40 to ~34 ms.
- **`@[specialize]` the scan loops**: the per-byte predicate was called indirectly once
  per byte; monomorphizing it into the loop recovered that. ~34 to ~20 ms.
- **First-byte `dispatch`**: peek the leading byte and jump to the branch instead of an
  `alt` chain that failed a keyword scan on every number. ~18% on canada.
- **Single-pass string scanner** (`GParser.stringLit`): one total escape-aware scanner
  instead of per-byte `foldMany`. twitter ~10 to ~3 ms, citm ~13.6 to ~8.1 ms.

## All example parsers

`lake exe bench` also times the other example grammars on generated inputs (grip-only
throughput, not a cross-library comparison):

| parser | input                | count  |  ms  |
|--------|----------------------|-------:|-----:|
| sexp   | 200 KB, 50k atoms    |  50000 | ~5.0 |
| lambda | 100 KB application   |    ok  | ~3.8 |
| http   | 80 KB, 10k headers   |  10000 | ~1.1 |
| toml   | cargo.lock, 72 KB    |    307 | ~0.8 |
| yaml   | 90 KB, 30k scalars   |  30001 | ~4.5 |
