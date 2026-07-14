# grip JSON benchmark

grip is a byte-level parser-combinator library for Lean 4 that carries a static grade on every
parser and a machine-checked soundness proof (see `grip-props/`). This file measures it against
other parser-combinator libraries on one fixed task, plus a hand-written scanner (the runtime
floor) and two different-model references.

## Task

Strict RFC-8259 validate and count leaf scalars, no DOM. Every parser rejects malformed numbers
(`00`, `1.`, `1e`), bad string escapes, unescaped control bytes, and trailing garbage, then
returns a leaf count: number / string / keyword = 1, object keys not counted, arrays and objects
sum their children. On the three files every same-task row returns the identical count, the
correctness gate:

| file                | bytes  | leaves | character |
|---------------------|-------:|-------:|-----------|
| `canada.json`       | 2.1 MB | 111130 | ~99% numbers |
| `citm_catalog.json` | 1.6 MB |  16390 | objects, keys, nesting |
| `twitter.json`      | 616 KB |  11600 | strings, Unicode, escapes |

The shared task definition each harness implements is `bench/cross-lang/TASK.md`.

## Method

Best-of-20, input preloaded into memory, timing excludes I/O, a barrier (`@[noinline]` /
`black_box` / `Sys.opaque_identity` / an `IO.Ref` sink) prevents the compiler eliding the parse.
The Lean rows are timed in-process by `bench/Bench.lean` (prim-parser by its own harness, same
technique); each cross-language harness times itself in its own runtime. Numbers are one session.

Machine: Apple Silicon (arm64-darwin), Darwin 25.2. **Every toolchain is native arm64**: Lean
v4.28.0, Rust 1.95, OCaml 5.3.0, and GHC 9.14.1 (installed via arm64 Homebrew; the Haskell rows
are not emulated).

Cross-runtime rows are context, not a controlled comparison: garbage collection, reference
counting, and value boxing differ per runtime. The controlled comparison is the Lean rows (grip,
Std.Parsec, prim-parser, hand), all native arm64 on the same toolchain.

## Same-task results (ms, lower is better)

Each row is a strict validator, non-allocating (no per-element list or `Vec`), bulk-scans string
bodies, and returns the leaf counts above. Sorted by `canada`.

| parser                                  | canada | citm  | twitter | runtime      |
|-----------------------------------------|-------:|------:|--------:|--------------|
| nom (Rust)                              |   1.70 |  1.24 |    0.49 | rustc 1.95   |
| hand-written scanner (Lean, no combinators) | 5.12 | 2.93 | 1.23 | Lean v4.28.0 |
| megaparsec (Haskell)                    |   9.86 |  4.45 |    1.72 | GHC 9.14.1   |
| attoparsec (Haskell)                    |  12.76 |  5.07 |    2.01 | GHC 9.14.1   |
| **grip** (Lean)                         |  19.38 |  7.73 |    2.88 | Lean v4.28.0 |
| Std.Internal.Parsec (Lean)              |  21.34 | 11.17 |    4.89 | Lean v4.28.0 |
| angstrom (OCaml)                        |  39.04 | 12.56 |    3.79 | OCaml 5.3.0  |
| prim-parser (Lean, deep-embedded)       |  71.01 | 32.29 |   10.89 | Lean v4.28.0 |

Versions: attoparsec 0.14.4, megaparsec 9.8.1, nom 7.1.3, angstrom 0.16.1; prim-parser is the
sibling `research/prim-parser` `G` (Graded) framework. Each uses its own library's idiomatic
combinators; none builds a DOM.

## Reading the numbers

grip is a mid-pack combinator parser, and the fastest one in the Lean set.

**Lean, same toolchain (the controlled set).** grip is the fastest combinator parser in Lean. It
beats `Std.Internal.Parsec` on every file (~1.1x canada, ~1.45x citm, ~1.7x twitter -- first-byte
`dispatch` and the single-pass `stringLit` scanner), and it beats **prim-parser, its own
predecessor, by ~3.6x** (19.4 vs 71.0 on canada). prim-parser's `G` framework is a deep-embedded,
reified combinator GADT interpreted at run time; grip is a shallow embedding -- each combinator is
a direct function over `ByteArray → Nat → ParseResult`, with no reified tree to walk. That
representation difference is the gap. grip sits ~3.8x above the hand-written Lean floor (5.12 ms),
which is the combinator overhead over raw byte recursion in the same runtime.

**Cross-language combinator libraries.** Both mature Haskell libraries beat grip on native arm64:
megaparsec (9.86) and attoparsec (12.76). angstrom (OCaml, 39.0) is slower than grip, ~3x
attoparsec, even after removing its per-array list allocation and switching to bulk string
scanning -- its per-combinator overhead dominates. Strict-eval native FP does not by itself make a
combinator library fast.

**Runtime floor.** nom (Rust) is ~11x grip on canada and leads every file. That gap is the
systems-language runtime (borrowed slices, no boxing, no reference counting), not the combinator
model; it holds across datasets.

**What grip offers.** grip is the fastest combinator parser in Lean and the only one here that
carries a static grade on every parser (the compile-time consumption/error contract), a
machine-checked soundness proof, and a kernel-total `fix`. It is beaten only by Rust (runtime) and
by two mature Haskell combinator libraries; it beats Lean's `Std.Internal.Parsec`, OCaml's
angstrom, and its own deep-embedded predecessor.

## Different model / task (context only)

Not the same-task comparison -- shown for completeness.

| parser                    | canada | citm | twitter | note                                             |
|---------------------------|-------:|-----:|--------:|--------------------------------------------------|
| lean4-parser (Lean, char) | 103.0  | 66.7 |   17.9  | `Char`-level (decodes UTF-8 per token); its byte mode is broken on v4.28.0 (fixed only in v4.32) |
| Lean.Json (Lean, DOM)     |  69.4  |  5.7 |    4.0  | builds a full `Lean.Json` tree -- strictly more work than validate-and-count |

lean4-parser (fgdorais, rev `d8428e2`) is `Char`-level here because its `ByteSlice` backend
back-tracks incorrectly on v4.28.0; decoding UTF-8 to `Char` per token is most of its cost.
`Lean.Json` is the built-in DOM parser -- on object-heavy citm it beats grip's validator, but it
is doing a different, heavier job.

## Fairness

Every same-task harness: (1) validates the RFC grammar (rejects bad numbers / escapes / control
bytes / trailing garbage); (2) is non-allocating -- no `sepBy` / `separated_list` / `sep_by1`
building a throwaway container per array; (3) bulk-scans safe string runs then branches on
escapes (the fast idiom grip, nom, and the hand scanner all use); (4) returns the identical
counts; (5) parses the grammar with the *library's own combinators*, not a hand-rolled byte
scanner. Four issues were fixed while assembling this table:

- angstrom's `sep_by1` built an int list per array -> non-allocating fold.
- the attoparsec / megaparsec string bodies validated byte-by-byte -> bulk `takeWhile` + escape branch.
- the Haskell rows were first measured under Rosetta (x86_64) -> re-measured on native arm64 GHC.
- the prim-parser harness was first a **hand-written byte scanner** (raw `arr[i]!` recursion,
  touching prim-parser only for whitespace) -> rewritten as a real `G`-framework combinator parser
  (`gJson`, `starFold`, `grecur`, `satisfy`/`takeWhile1`). That correction moved prim-parser from a
  spurious 8 ms (a hand scanner in disguise) to its true 71 ms.

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

`<file>` is one of `bench/data/{canada.json,citm_catalog.json,twitter.json}`. The prim-parser
harness path-requires the sibling `research/prim-parser` repo and pulls mathlib from the prebuilt
cache (`lake exe cache get`); its `.lake` is large and git-ignored. On arm64 macOS install native
GHC with `brew install ghc cabal-install` so the Haskell rows are not run under Rosetta.

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

- **Single-constructor result** (`Except Err (α × Nat)` to `ParseResult α`): one heap object per
  success, not two. ~40 to ~34 ms.
- **`@[specialize]` the scan loops**: the per-byte predicate was called indirectly once per byte;
  monomorphizing it into the loop recovered that. ~34 to ~20 ms.
- **First-byte `dispatch`**: peek the leading byte and jump to the branch instead of an `alt`
  chain that failed a keyword scan on every number. ~18% on canada.
- **Single-pass string scanner** (`GParser.stringLit`): replaced a per-byte `foldMany` string
  body with one total escape-aware scanner; twitter ~10 to ~3 ms, citm ~13.6 to ~8.1 ms.

grip sits ~3.8x above the hand-written Lean floor (the combinator overhead in the same runtime)
and ~3.6x below prim-parser's reified `G` interpreter -- the shallow-versus-deep embedding choice
is the dominant factor between the two Lean combinator libraries.

## All example parsers

`lake exe bench` also times the other example grammars on generated inputs (grip-only throughput,
not a cross-library comparison):

| parser | input                | count  |  ms  |
|--------|----------------------|-------:|-----:|
| sexp   | 200 KB, 50k atoms    |  50000 | ~5.0 |
| lambda | 100 KB application   |    ok  | ~3.8 |
| http   | 80 KB, 10k headers   |  10000 | ~1.1 |
| toml   | cargo.lock, 72 KB    |    307 | ~0.8 |
| yaml   | 90 KB, 30k scalars   |  30001 | ~4.5 |
