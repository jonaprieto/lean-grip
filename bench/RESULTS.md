# grip benchmark results

Input: `bench/data/canada.json` (~2.1 MB, the standard nativejson-benchmark GeoJSON
file). Machine: Apple Silicon, arm64-darwin. Toolchain: `leanprover/lean4:v4.28.0`.

Methodology: best-of-20 wall time via `IO.monoNanosNow`, self-timed, all on the *same*
file and machine. grip and `Lean.Json` are timed by `lake exe bench` (same toolchain).
The lean4-parser number is its shipped `examples/JSON.lean` validator
(fgdorais/lean4-parser, toolchain v4.32.0-rc1) run through the same harness. grip's
parser is `examples/Json.lean`, built entirely from grip combinators (`fix`, `dispatch`,
`seqR`, `alt`, `foldMany`, `takeWhile1`) -- not a hand-rolled scanner.

Read the `work` column before comparing: grip and lean4-parser **validate** the input
(grip also counts leaves, cheap `Nat` adds); `Lean.Json` builds a **full DOM** (a
`Lean.Json` tree), which is strictly more work.

| parser                        | parse_ms | work             | notes                                            |
|-------------------------------|---------:|------------------|--------------------------------------------------|
| grip (combinators)            |    ~34   | validate + count | byte-level; `examples/Json.lean`, pure combinators |
| Lean.Json (core, built-in)    |    ~68   | full DOM build   | Lean's `Lean.Json.parse`; builds the tree        |
| lean4-parser (fgdorais)       |   ~273   | validate         | `SimpleParser String.Slice Char`; `sepBy` allocates |

Apples-to-apples (both validate, no DOM): grip is about **8x faster than lean4-parser**
on the competitor's own unmodified JSON example. grip's validator is also ~2x faster
than `Lean.Json`, but that is not the same task -- `Lean.Json` materialises a tree grip
does not build, so treat it as context, not a like-for-like win.

## First-byte dispatch

The JSON value parser was `alt keyword (alt number (alt string (alt array object)))`. On
canada.json (~99% numbers) every value first *failed* a keyword scan -- a wasted
sub-parse plus an error allocation -- before reaching the number branch. Replacing the
`alt` chain with `GParser.dispatch` (peek the leading byte, jump straight to the branch)
removed that per-node waste and cut the parse from ~49ms to ~40ms (about 18%).

## Single-constructor result

The core result was `Except Err (α × Nat)`: a successful step allocated `Except.ok`
wrapping a `Prod`, two heap objects. Replacing it with one constructor,
`ParseResult α = ok value offset | error e`, makes a success a single object and took the
parse from ~40ms to ~34ms (about 15%). Every combinator, the `cwit`/`ewit`/`swit`
witnesses, and the whole `grip-props` metatheory were ported to the new shape with no
loss of features and no new `sorry`.

## All example parsers

`lake exe bench` times every example parser (JSON on canada.json, the rest on inputs
generated at startup), best-of-20 on the same machine. Throughput is input size over
best time.

| parser | input                | count  |  ms  | MB/s |
|--------|----------------------|-------:|-----:|-----:|
| json   | canada.json, 2.1 MB  | 111130 | ~34  | ~62  |
| sexp   | 200 KB, 50k atoms    |  50000 | ~9.0 | ~22  |
| lambda | 100 KB application   |    ok  | ~6.0 | ~17  |
| http   | 80 KB, 10k headers   |  10000 | ~1.5 | ~53  |
| toml   | 200 KB, 20k entries  |  20000 | ~7.1 | ~28  |
| yaml   | 90 KB, 30k scalars   |  30001 | ~7.3 | ~12  |

`count` is the parser's own result on the input (leaf nodes for JSON, list length for the
others; `lambda` reports a success flag). These stress the shared combinators (`fix`,
`dispatch`, `capture`, `many`) across recursive, line-oriented, and nested grammars.

## Where grip's time goes

To attribute the gap to a fast native combinator library, the same leaf-count parse was
run four ways on canada.json, best-of-20, same machine (all counted 111130):

| approach                                   | parse_ms | difference explained                         |
|--------------------------------------------|---------:|----------------------------------------------|
| Rust `nom` (byte-level, `fold_many0`)      |   ~2.0ms  | monomorphized, borrowed slices, no boxing    |
| hand-written Lean scanner (no combinators) |  ~13.2ms  | the Lean runtime floor                       |
| **grip today** (single-constructor result) |   ~34ms   | grip's model, one heap object per step       |
| grip before (`Except Err (α × Nat)`)       |   ~40ms   | two heap objects per step (`Except` + `Prod`) |

Reading the steps:

- **Result boxing (~40 to ~34):** *done.* Merging `Except Err (α × Nat)` into a single
  `ParseResult α = ok value offset | error e` constructor removed one allocation per step,
  worth about 15%. This is the shipped representation; every combinator and every
  soundness proof was ported to it.
- **Combinator indirection (~34 to ~13):** the largest remaining share. Each combinator is a
  `GParser` struct whose `run` is a closure; Lean calls through those closures instead
  of inlining the grammar into one flat function the way Rust monomorphizes `nom`.
  Closing this needs a monomorphizing or CPS redesign, not a result-type tweak.
- **Language floor (~13 to ~2):** reference counting, bounds-checked `ByteArray`
  indexing, and no monomorphization. Even a hand-written Lean scanner stays ~6.5x off
  `nom`; that part is the runtime, not grip.

So grip is the fast *combinator* option in Lean, and a hand-written scanner or a
systems-language library like `nom` will beat it -- see the README's "When to reach for
grip". Haskell's attoparsec (~19.5ms, DOM build, nativejson-benchmark) is a published
cross-language point, not run here.

The `nom` parser used here is a byte-level leaf-counter matching grip's semantics
(validate, count leaves, keys not counted, `fold_many0` so no per-element `Vec`); it is
not shipped in this repo (no Rust in CI).

Update this file by running `lake exe bench` and `sh bench/mkchart.sh`.
