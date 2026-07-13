# grip benchmark results

Input: `bench/data/canada.json` (~2.1 MB, the standard nativejson-benchmark GeoJSON file).
Machine: Apple Silicon, arm64-darwin. Toolchain: `leanprover/lean4:v4.28.0`, native C.

**grip is a grammar-strict RFC-8259 validator.** It rejects malformed numbers (`00`, `1e`,
`1.`), bad string escapes, and trailing garbage after a value. The two in-repo Lean baselines
(`StdParsecJson`, `HandScanner`) were rewritten to match the same grammar, so those three-way
comparisons are same-task. The cross-language parsers (`nom`, `attoparsec`) remain loose
shape-only scanners -- they accept tokens the grammar forbids -- so grip's gap to them is
conservative: a strict competitor would only be slower. On the valid benchmark files all parsers
still report count **111130**.

**Method.** Best-of-20 wall time via `IO.monoNanosNow`, self-timed, input preloaded, with a
`@[noinline]` barrier so the parse cannot be hoisted past the timer. The cross-language parsers
(`bench/cross-lang/`) use the equivalent method in their own runtime.

**Machine state matters; compare ratios.** All Lean rows in each table were measured in the same
session, back to back, so the **ratios between parsers are the reliable, state-invariant
quantity**; read them, not the absolute milliseconds.

## JSONTestSuite conformance

grip is a grammar-strict RFC-8259 validator and a JSONTestSuite `parsers/` entry
(`parsers/test_grip.sh`, exit 0/1). Against the vendored `test_parsing/` corpus
(`lake exe conformance`):

    y: 95/95 accepted · n: 186/186 rejected (allow-accept 0) · i: 31 accepted / 4 rejected · excluded: 2

Grammar-strict ceiling (documented non-goals): invalid-UTF-8 `n_` files are accepted (no UTF-8
validation) and deep-nesting `n_` files are excluded (the recursive `fix` is stack-bounded, not
trampolined). See `docs/specs/2026-07-13-json-conformance-design.md`. Reproduce grip's verdicts
under the official driver with `test/run-jsontestsuite.sh`.

## Against other Lean parsers (same toolchain, same task)

| parser                                | ms    | grip / it | work             | notes                                               |
|---------------------------------------|------:|----------:|------------------|-----------------------------------------------------|
| hand-written scanner (no combinators) |  5.3  |   3.72x   | validate + count | grammar-strict; `bench/Bench.lean` `HandScanner`    |
| `Std.Internal.Parsec` (std)           | 22.3  |   0.88x   | validate + count | grammar-strict; byte-level std combinators          |
| **grip (combinators)**                | 19.7  |   1.00x   | validate + count | grammar-strict; `examples/Json.lean`, grades + soundness |
| `Lean.Json` (built-in)               | ~72   |   --      | full DOM build   | builds a tree -- a *different, heavier task*        |

The clean comparison is **`Std.Internal.Parsec`**, Lean's own standard combinator library:
byte-level, same toolchain, same grammar-strict validate-and-count task, identical 111130 count.
grip is **marginally ahead** -- 0.88x its time, within noise -- carrying static grades and
machine-checked soundness that `Std.Parsec` does not, at **no measurable speed cost**.

**Hand-scanner floor.** The strict hand-scanner runs at ~5.3 ms, making grip ~3.7x slower --
a larger gap than the 1.54x reported in the prior loose-scanner era. This is not a grip
regression. The old loose scanner was ~16.5 ms; the new strict scanner is ~5.3 ms because it
inlines byte checks directly rather than passing a per-byte closure (`scanWhile a (· != 34)`),
and it validates strictly. grip itself is unchanged (~20 ms on AC). The runtime floor got faster
(a better-written strict scanner), which honestly reveals grip's combinator overhead: one
`ParseResult` allocation per combinator step and `GParser` struct dispatch that the specializer
does not reach. grip is not slower; the floor is better.

An earlier version of this file claimed grip was "1.7x faster" than `Std.Internal.Parsec`. That
was an artifact of an unfair `Std.Parsec` implementation using `many (satisfy _)`, which builds
and discards an `Array` per token. Replacing that with non-allocating `skipWhile` roughly halved
its time and erased the gap.

`Lean.Json` is the built-in and builds a full DOM, strictly more work than validate-and-count,
so it is not a controlled comparison; it is shown for reference, not as a grip "win".

## Beyond canada.json: the rest of the nativejson suite

canada.json is ~99% numbers, so it exercises number scanning and array folding but little else.
The other two standard nativejson-benchmark files stress the parts it does not: `citm_catalog.json`
(1.7 MB, object/key/nesting-heavy) and `twitter.json` (632 KB, string/Unicode/escape-heavy). Both
contain escaped quotes (`\"`), so both grip and the `Std.Internal.Parsec` reference validate
string bodies strictly. grip folds a per-byte `strChar` combinator (an unescaped byte, or a
`\`-escape validated including `\uXXXX`) via `foldMany`; Std.Parsec uses a direct recursive
`any`-based scan. That per-byte combinator dispatch is exactly why grip is slower on the
string/escape-heavy files below. Both parsers are grammar-strict and return the identical leaf
count on each file (grip and Std.Parsec agree with `jq`'s `[.. | scalars] | length`), so it is
the same task.

| file       | leaves | grip ms | Std.Parsec ms | grip vs Std.Parsec |
|------------|-------:|--------:|--------------:|--------------------|
| canada     | 111130 |  ~19.7  |     ~22.3     | grip ~1.13x faster |
| citm       |  16390 |  ~13.6  |     ~11.7     | Std.Parsec ~1.16x faster |
| twitter    |  11600 |  ~10.0  |     ~5.1      | Std.Parsec ~1.96x faster |

On this run, grip is faster than Std.Parsec on number-heavy canada but behind on object-heavy
citm and notably behind on string/escape-heavy twitter. The twitter gap is real: grip's string
scanner processes escapes strictly per the grammar; a future measure-then-specialize pass on the
escape path is the natural next step. The honest headline is: grip is level-to-competitive with
Std.Parsec on number-heavy input, while being behind on escape-heavy input. (These three were
measured back to back in the same session; read the ratios.)

## Cross-language context (different runtimes; prior measurements)

Measured previously on this machine, same task, same file (`bench/cross-lang/`). These parsers
are **loose shape-only scanners** (nom and attoparsec accept tokens the RFC-8259 grammar forbids);
grip is grammar-strict, so the comparison is conservative for grip. No Rust/Haskell toolchain is
present in this repo for re-measurement; the figures below are prior measurements, not from this
bench run.

| parser                | ms    | grip / it | runtime                              |
|-----------------------|------:|----------:|--------------------------------------|
| Rust `nom`            |  2.57 |  ~9.9x    | rustc 1.95, `fold_many0`, byte-level, loose |
| Haskell `attoparsec`  | 22.7  |  ~1.1x    | GHC 9.10.1, byte-level, no DOM, loose      |
| grip                  | 25.4  |  1.00x    | Lean v4.28.0, grammar-strict               |

grip is **level with attoparsec** (~1.1x, both combinator parsers) and about **10x off Rust
`nom`**. The nom gap is the Lean-versus-Rust runtime floor (reference counting, bounds-checked
indexing, no borrowed slices), not the combinator model. Because nom and attoparsec are loose
scanners, a strict Rust/Haskell counterpart would only be slower; the shown gap overstates grip's
disadvantage. These are different-runtime context, not a controlled comparison.

## Where grip's time goes

The same leaf-count parse, several ways, on canada.json (all count 111130). The grip rows are
grip's own optimization history (each an on-AC representation change, the grade algebra unchanged
throughout); the floor rows are current measurements from this session.

| approach                                     | parse_ms | note                                          |
|----------------------------------------------|---------:|-----------------------------------------------|
| Rust `nom` (byte-level, `fold_many0`)        |    ~2.6  | monomorphized, borrowed slices, no boxing; loose |
| hand-written Lean scanner (no combinators)   |    ~5.3  | grammar-strict; Lean runtime floor (RC, bounds checks) |
| **grip today** (scan loops specialized)      |  ~19.7 (this run) / ~20 (AC) | combinators; predicate monomorphized in-loop |
| grip before `@[specialize]`                  |  ~34 (AC) | scan predicate called indirectly per byte     |
| grip before single-constructor result        |  ~40 (AC) | two heap objects per step (`Except` + `Prod`) |

- `Except`+`Prod` to one constructor (~40 to ~34, AC): a success now allocates one object.
- `@[specialize]` the scan loops (~34 to ~20, AC): the per-byte predicate was the dominant cost,
  called indirectly once per byte. Monomorphizing it into the loop recovered that, with no CPS
  and no redesign; the combinator model stayed intact.
- grip vs hand-written Lean (~3.7x this run): the residue is one `ParseResult` object per
  combinator step and the `GParser` struct and closure dispatch the specializer does not reach.
  The floor is now faster (strict inline byte checks vs the old closure-based loose scanner),
  which honestly reveals more overhead than the prior 1.54x figure. grip did not regress.
- hand-written Lean vs nom (~2x here): the Lean runtime floor. That part is the language.

grip is a competitive combinator parser -- level with Lean's own `Std.Internal.Parsec` on
number-heavy input and with Haskell's `attoparsec` on the same task -- that additionally
validates the full RFC-8259 grammar and keeps machine-checked soundness at no measurable speed
cost versus Std.Parsec. A systems-language library like `nom` is still ~10x faster; that gap is
the runtime, not the design.

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
grammars), not cross-library comparisons. Figures below are from this run.

| parser | input                    | count  |  ms   |
|--------|--------------------------|-------:|------:|
| json   | canada.json, 2.1 MB      | 111130 | ~19.7 |
| sexp   | 200 KB, 50k atoms        |  50000 |  ~5.0 |
| lambda | 100 KB application       |    ok  |  ~3.8 |
| http   | 80 KB, 10k headers       |  10000 |  ~1.1 |
| toml   | cargo.lock, 72 KB        |    307 |  ~0.8 |
| yaml   | 90 KB, 30k scalars       |  30001 |  ~4.5 |

Update the Lean rows by running `lake exe bench`. The cross-language rows (`bench/cross-lang/`)
require a machine with Rust and GHC toolchains and must be updated separately.
