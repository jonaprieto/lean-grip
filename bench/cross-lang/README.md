# Cross-language JSON leaf-counter benchmarks

Reference implementations of grip's `examples/Json.lean` task in other languages, so the
cross-language numbers in `bench/RESULTS.md` are reproducible rather than cited. Each does the
**same task**: parse `bench/data/canada.json` (2.1 MB), validate structure, count leaf scalars
(number / string / keyword = 1 leaf; object keys not counted; containers sum their children).
All three return the identical count **111130** — a different count would mean a different task.

These are not built in CI (they need a Rust or Haskell toolchain); run them by hand.

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
