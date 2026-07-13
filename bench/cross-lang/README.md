# Cross-project JSON leaf-counter benchmarks

Reference implementations of grip's `examples/Json.lean` task in other libraries/languages, so
the comparison numbers in `bench/RESULTS.md` are reproducible rather than cited. Each does the
**same task**: parse `bench/data/canada.json` (2.1 MB), validate structure, count leaf scalars
(number / string / keyword = 1 leaf; object keys not counted; containers sum their children).
All return the identical count **111130** — a different count would mean a different task.

These are not built in the main CI (they need a Rust or Haskell toolchain, or a different Lean
revision); run them by hand.

## lean4-parser (fgdorais), same compiler as grip

```sh
cd bench/cross-lang/lean4-parser && lake update && lake build && .lake/build/bin/L4pBench
```

Pinned to lean4-parser revision `d8428e2`, its last commit on grip's own toolchain
(`v4.28.0`), so this runs on the **same compiler** as grip — no cross-toolchain confound.
Char-level (`SimpleParser String.Slice Char`, the library's shipped idiom), using the
non-allocating `foldl` accumulator rather than the allocating `sepBy` — lean4-parser at its best
here. It is not a byte parser: `String.Slice` decodes UTF-8 to `Char`, so it does more per token
than a byte-level parser, and lean4-parser is a general-purpose combinator library, not tuned for
byte throughput. (Its byte-level `ByteSlice` stream is broken on `v4.28.0` — a backtracking
off-by-`start` bug fixed only in `v4.32.0-rc1` — so char-level is the only working mode on grip's
compiler.) Measured ~149 ms; grip is ~6x faster on the same compiler and task.

## Rust `nom`

```sh
cd bench/cross-lang/nom && cargo run --release
```

Byte-level (`&[u8]`), `fold_many0` for arrays/objects (no per-element `Vec`). nom 7.1.3,
rustc 1.95.0. Prints `count=111130` and `best_ms` (best of 20 in-process runs, parse only).

## Haskell `attoparsec`

```sh
cd bench/cross-lang/atto && cabal run atto-bench
```

`Data.Attoparsec.ByteString` (byte-level, strict `ByteString`), counts into an `Int` — no DOM
built. attoparsec 0.14.4, GHC 9.10.1. Prints `count=111130` and `best_ms`.

## Method and caveats

Each measures the parse only (file preloaded into memory, timing excludes I/O), best of 20,
with a barrier so the compiler cannot elide the parse. They run in different runtimes, so these
are cross-language *context*, not a controlled comparison: the Lean-vs-Rust gap is the runtime
floor (reference counting, bounds-checked indexing), not the combinator model. Absolute numbers
depend on machine state; compare ratios. See `bench/RESULTS.md` for the numbers and the
controlled (same-toolchain) Lean comparison.
