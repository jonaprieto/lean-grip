# grip benchmark results

Input: `bench/data/canada.json` (~2.1 MB, the standard nativejson-benchmark GeoJSON file).
Machine: Apple Silicon, arm64-darwin. Toolchain: `leanprover/lean4:v4.28.0`, native C.

**Same task across every parser.** Validate the JSON structure and count leaf scalars: 1 per
number, string, or keyword (`true`/`false`/`null`); object keys are not counted; arrays and
objects sum their children. Every parser below returns the identical count **111130** -- a
different count would be a different task and the comparison would be void. Each library uses
its own *best* idiomatic implementation of that task (see the note on `Std.Internal.Parsec`
below); we do not handicap a competitor.

**Method.** Best-of-20 wall time via `IO.monoNanosNow`, self-timed, input preloaded, with a
`@[noinline]` barrier so the parse cannot be hoisted past the timer. The cross-language parsers
(`bench/cross-lang/`) use the equivalent method in their own runtime.

**Machine state matters; compare ratios.** These numbers were taken in one session on battery
(not AC) with some background load, so every absolute figure is about 1.25x an on-AC baseline
(grip parses in ~20 ms on AC, ~25 ms here). All rows in a table were measured in the *same*
state, back to back, so the **ratios between parsers are the reliable, state-invariant quantity**;
read them, not the absolute milliseconds.

## Against other Lean parsers (same toolchain, same task)

| parser                          | ms   | grip / it | work             | notes                                              |
|---------------------------------|-----:|----------:|------------------|----------------------------------------------------|
| hand-written scanner (no combinators) | 16.5 | 1.54x | validate + count | the Lean runtime floor; `bench/Bench.lean` `HandScanner` |
| `Std.Internal.Parsec` (std)     | 24.0 | 1.06x | validate + count | byte-level std combinators, `skipWhile` (its best) |
| **grip (combinators)**          | 25.4 | 1.00x | validate + count | byte-level; `examples/Json.lean`, grades + soundness |
| `Lean.Json` (built-in)          | ~99  |   --      | full DOM build   | builds a tree -- a *different, heavier task*        |
| `lean4-parser` (fgdorais)       | ~149 | 0.17x (grip ~6x faster) | validate + count | `Char`-level, general-purpose; same compiler v4.28.0 |

The clean comparison is **`Std.Internal.Parsec`**, Lean's own standard combinator library:
byte-level, same toolchain, same validate-and-count task, identical 111130 count. grip and it
are **level** -- grip is about 1.06x its time, i.e. within noise, marginally behind. This is the
honest headline: grip carries static grades and machine-checked soundness that `Std.Parsec` does
not, at **no measurable speed cost**.

An earlier version of this file claimed grip was "1.7x faster" than `Std.Internal.Parsec`. That
was an artifact of an unfair `Std.Parsec` implementation: it scanned tokens with
`many (satisfy _)`, which builds and discards an `Array` per token. Replacing that with the
non-allocating `skipWhile` -- `Std.Parsec`'s own best idiom -- roughly halved its time (from
~46 ms to ~24 ms) and erased the gap. The corrected comparison is level.

`Lean.Json` is the built-in and builds a full DOM, strictly more work than validate-and-count,
so it is not a controlled comparison; it is shown for reference, not as a grip "win".

**`lean4-parser` (fgdorais)** is measured on grip's *own* compiler, `v4.28.0` -- its last
compatible revision `d8428e2` -- so there is no cross-toolchain confound. grip is about **6x
faster** (~25 vs ~149 ms), same task, identical 111130 count. Two caveats keep this honest, and
they are the whole of the gap:

- lean4-parser is `Char`-level (`SimpleParser String.Slice Char`): `String.Slice` decodes UTF-8
  to `Char`, so it does strictly more per token than a byte parser. Its byte-level `ByteSlice`
  stream is broken on `v4.28.0` (a backtracking off-by-`start` bug, fixed only in `v4.32.0-rc1`),
  so `Char`-level is the only working mode on grip's compiler.
- **lean4-parser is a general-purpose combinator library, not tuned for byte throughput.** It
  prioritizes generality (parse any `Stream`) and correctness over raw speed. Comparing byte
  throughput understates its design goals; the 6x is a byte-vs-char and design-priority gap, not
  a claim that grip's combinator model is 6x better.

We still gave it its best on this compiler: the non-allocating `foldl` accumulator, not the
allocating `sepBy` of the shipped example. A prior "14x faster" figure was measured on a
different toolchain (`v4.32.0-rc1`) against the allocating example; both effects are removed here.
(For reference, the identical hand-written scanner runs ~16.6 ms on `v4.28.0` and ~18.4 ms on
`v4.32.0-rc1`, so the toolchain itself accounts for only ~11%.)

## Beyond canada.json: the rest of the nativejson suite

canada.json is ~99% numbers, so it exercises number scanning and array folding but little else.
The other two standard nativejson-benchmark files stress the parts it does not: `citm_catalog.json`
(1.7 MB, object/key/nesting-heavy) and `twitter.json` (632 KB, string/Unicode/escape-heavy). Both
contain escaped quotes (`\"`), so this needed escape-aware string scanning in both grip
(`GParser.takeStringBody`, a total scanner) and the `Std.Internal.Parsec` reference (an
iterator-based scan, its best -- not a per-byte monadic loop). Both parsers return the identical
leaf count on each file (grip and Std.Parsec agree with `jq`'s `[.. | scalars] | length`), so it
is the same task.

| file       | leaves | grip ms | Std.Parsec ms | grip vs Std.Parsec |
|------------|-------:|--------:|--------------:|--------------------|
| canada     | 111130 |   ~18   |     ~17       | 1.05x (level)      |
| citm       |  16390 |   ~8.1  |     ~10.2     | grip ~1.25x faster |
| twitter    |  11600 |   ~3.3  |     ~3.6      | grip ~1.1x faster  |

grip is **level-to-faster than `Std.Internal.Parsec` across the suite**: level on number-heavy
canada, and about 1.1--1.25x faster on the object- and string-heavy files, where grip's
first-byte `dispatch` and specialized scanners beat Std.Parsec's per-byte monadic object and
string navigation. So the "level" headline is the number-heavy worst case for grip; on realistic
mixed JSON it is ahead. (These three were measured back to back on AC; read the ratios.)

## Cross-language context (different runtimes; real, not cited)

Measured on this machine, same task, same file (`bench/cross-lang/`, reproducible by hand):

| parser                | ms    | grip / it | runtime                          |
|-----------------------|------:|----------:|----------------------------------|
| Rust `nom`            | 2.57  | ~9.9x     | rustc 1.95, `fold_many0`, byte-level |
| Haskell `attoparsec`  | 22.7  | ~1.1x     | GHC 9.10.1, byte-level, no DOM   |
| grip                  | 25.4  | 1.00x     | Lean v4.28.0                     |

grip is **level with attoparsec** (~1.1x, both combinator parsers) and about **10x off Rust
`nom`**. The nom gap is the Lean-versus-Rust runtime floor (reference counting, bounds-checked
indexing, no borrowed slices), not the combinator model: it holds on s-expressions too, so it
does not narrow with the grammar. These are different-runtime context, not a controlled
comparison. The earlier attoparsec figure (~19.5 ms) was cited from a published cross-machine
DOM benchmark; the ~22.7 ms here is our own controlled same-task, same-machine measurement.

## Where grip's time goes

The same leaf-count parse, several ways, on canada.json (all count 111130). The grip rows are
grip's own optimization history (each an on-AC representation change, the grade algebra unchanged
throughout); the floor rows are this session's measurements.

| approach                                     | parse_ms | note                                          |
|----------------------------------------------|---------:|-----------------------------------------------|
| Rust `nom` (byte-level, `fold_many0`)        |   ~2.6   | monomorphized, borrowed slices, no boxing     |
| hand-written Lean scanner (no combinators)   |  ~16.5   | the Lean runtime floor (RC, bounds checks)    |
| **grip today** (scan loops specialized)      |  ~20 (AC) / ~25 (here) | combinators; predicate monomorphized in-loop |
| grip before `@[specialize]`                  |  ~34 (AC) | scan predicate called indirectly per byte     |
| grip before single-constructor result        |  ~40 (AC) | two heap objects per step (`Except` + `Prod`) |

- `Except`+`Prod` to one constructor (~40 to ~34, AC): a success now allocates one object.
- `@[specialize]` the scan loops (~34 to ~20, AC): the per-byte predicate was the dominant cost,
  called indirectly once per byte. Monomorphizing it into the loop recovered that, with no CPS
  and no redesign; the combinator model stayed intact.
- grip vs hand-written Lean (~1.54x): the residue is one `ParseResult` object per combinator step
  and the `GParser` struct and closure dispatch the specializer does not reach.
- hand-written Lean vs nom (~6x here): the Lean runtime floor. That part is the language.

grip is a competitive combinator parser -- level with Lean's own `Std.Internal.Parsec` and with
Haskell's `attoparsec` on the same task -- that additionally keeps its grades and its
machine-checked soundness at no measurable speed cost. A systems-language library like `nom` is
still ~10x faster; that gap is the runtime, not the design.

## First-byte dispatch

The JSON value parser used to be `alt keyword (alt number (alt string (alt array object)))`.
canada.json is about 99% numbers, so every value first failed a keyword scan, a wasted sub-parse
plus an error allocation, before it reached the number branch. Replacing the `alt` chain with
`GParser.dispatch` (peek the leading byte, jump straight to the branch) removed that per-node
waste, about 18% on AC.

## Single-constructor result

The core result used to be `Except Err (α × Nat)`, so a successful step allocated an `Except.ok`
wrapping a `Prod`, two heap objects. Collapsing it to `ParseResult α = ok value offset | error e`
makes a success a single object, ~40 to ~34 ms on AC. Every combinator, the witnesses, and the
`grip-props` metatheory were ported with no loss of features and no new `sorry`.

## Specialize the scan loops

The largest single win. `scanFwd`/`foldFwd`/`natFwd` are the tight inner loops; as plain `def`s
their function arguments (the byte predicate, the fold step) were closures called indirectly once
per byte across 2 MB. Marking them `@[specialize]` (and `@[inline]` on `weaken`/`weakenFallible`)
lets Lean monomorphize a statically-known predicate straight into the loop, so the per-byte call
disappears: ~34 to ~20 ms on AC, about 40%. A one-word attribute, the combinator model intact.

## All example parsers

`lake exe bench` times every example parser, best-of-20. JSON runs on canada.json and TOML on a
real `Cargo.lock` (vendored under `bench/data/`); the rest run on inputs generated at startup.
These are grip-only throughput (its combinators across recursive, line-oriented, and nested
grammars), not cross-library comparisons. Figures below are the on-AC baseline; on battery/loaded
they scale up by ~1.25x uniformly.

| parser | input                    | count  |  ms  |
|--------|--------------------------|-------:|-----:|
| json   | canada.json, 2.1 MB      | 111130 | ~20  |
| sexp   | 200 KB, 50k atoms        |  50000 | ~5.7 |
| lambda | 100 KB application       |    ok  | ~3.7 |
| http   | 80 KB, 10k headers       |  10000 | ~1.0 |
| toml   | cargo.lock, 72 KB        |    307 | ~0.8 |
| yaml   | 90 KB, 30k scalars       |  30001 | ~4.4 |

Update this file by running `lake exe bench` (Lean parsers), and the `bench/cross-lang/` commands
(nom, attoparsec) on a machine with those toolchains.
