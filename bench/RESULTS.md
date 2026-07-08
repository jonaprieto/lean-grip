# grip benchmark results

Input: `bench/data/canada.json` (~2.1 MB, the standard nativejson-benchmark GeoJSON
file). Machine: Apple Silicon, arm64-darwin, on AC power (battery / Low Power Mode caps
the CPU frequency and inflates every figure ~1.4x uniformly). Toolchain:
`leanprover/lean4:v4.28.0`.

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
| grip (combinators)            |    ~20   | validate + count | byte-level; `examples/Json.lean`, pure combinators |
| Lean.Json (core, built-in)    |    ~68   | full DOM build   | Lean's `Lean.Json.parse`; builds the tree        |
| lean4-parser (fgdorais)       |   ~273   | validate         | `SimpleParser String.Slice Char`; `sepBy` allocates |

Apples-to-apples (both validate, no DOM): grip is about **14x faster than lean4-parser**
on the competitor's own unmodified JSON example, and ~3.5x faster than `Lean.Json` (which
does more -- it builds a tree grip does not, so treat that as context). At ~20ms grip is
level with Haskell's attoparsec (see below).

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

## Specialize the scan loops (the big one)

`scanFwd`/`foldFwd`/`natFwd` -- the tight inner loops that walk the bytes -- were plain
recursive `def`s, so their function arguments (the byte predicate, the fold step) were
*closures called indirectly once per byte* over the whole 2 MB. Marking them
`@[specialize]` (and `@[inline]` on the `weaken`/`weakenFallible` wrappers) makes Lean
monomorphize a statically-known predicate like `Ascii.isWs` straight into the loop, so
the per-byte call disappears. canada.json dropped from ~34ms to **~20ms** (about 40%).

This is the fix for what an earlier draft of this file wrongly called the "combinator
indirection" wall (claiming it needed a CPS or monomorphizing rewrite). It did not: a
one-word attribute on the three scan loops recovered most of the gap while keeping the
combinator model intact. grip is now level with attoparsec (~19.5ms) and ~1.5x off a
hand-written Lean scanner.

## All example parsers

`lake exe bench` times every example parser (JSON on canada.json, the rest on inputs
generated at startup), best-of-20 on the same machine. Throughput is input size over
best time.

| parser | input                | count  |  ms  | MB/s |
|--------|----------------------|-------:|-----:|-----:|
| json   | canada.json, 2.1 MB  | 111130 | ~20  | ~107 |
| sexp   | 200 KB, 50k atoms    |  50000 | ~5.9 | ~34  |
| lambda | 100 KB application   |    ok  | ~3.7 | ~27  |
| http   | 80 KB, 10k headers   |  10000 | ~1.0 | ~80  |
| toml   | 200 KB, 20k entries  |  20000 | ~5.4 | ~37  |
| yaml   | 90 KB, 30k scalars   |  30001 | ~4.5 | ~20  |

`count` is the parser's own result on the input (leaf nodes for JSON, list length for the
others; `lambda` reports a success flag). These stress the shared combinators (`fix`,
`dispatch`, `capture`, `many`) across recursive, line-oriented, and nested grammars. All
got faster from the single-constructor result and the scan-loop `@[specialize]`.

### Does the nom gap generalize past JSON?

Yes, and it narrowed after the scan-loop specialization. A `nom` S-expression
atom-counter on the same input grip's sexp bench uses (`"(" ++ "sym " * 50000 ++ ")"`,
count 50000) runs in ~0.7ms; grip's sexp is ~5.9ms, about **8x**. JSON is ~10x (grip
~20ms, nom ~2ms). What is left is the Lean-vs-Rust runtime floor (reference counting,
bounds-checked indexing, no borrowed slices) -- not the combinator model. (The `nom`
parsers are not shipped -- no Rust in CI.)

## Where grip's time goes

The same leaf-count parse, several ways, canada.json, best-of-20, on AC (all count
111130):

| approach                                   | parse_ms | note                                          |
|--------------------------------------------|---------:|-----------------------------------------------|
| Rust `nom` (byte-level, `fold_many0`)      |   ~2.0ms  | monomorphized, borrowed slices, no boxing     |
| hand-written Lean scanner (no combinators) |  ~13ms    | the Lean runtime floor                        |
| **grip today** (scan loops specialized)    |  ~20ms    | combinators; predicate monomorphized in-loop  |
| grip before `@[specialize]`                |  ~34ms    | scan predicate called indirectly per byte     |
| grip before single-constructor result      |  ~40ms    | two heap objects per step (`Except` + `Prod`) |

Reading the steps:

- **`Except`+`Prod` to one constructor (~40 to ~34):** a success now allocates one object.
- **`@[specialize]` the scan loops (~34 to ~20):** the per-byte predicate was the dominant
  cost, called indirectly once per byte. Monomorphizing it into the loop recovered it --
  no CPS or redesign, the combinator model stayed intact. An earlier draft wrongly called
  this a "combinator indirection wall" needing a rewrite; it was a one-word attribute.
- **grip ~20 vs hand-written Lean ~13 (~1.5x):** the residue -- one `ParseResult` object per
  combinator step and the `GParser` struct/closure dispatch the specializer does not reach.
- **hand-written Lean ~13 vs nom ~2:** the Lean runtime floor (RC, bounds checks, no
  borrowed slices). That part is the language, not grip.

grip now sits level with Haskell's attoparsec (~19.5ms, DOM build, nativejson-benchmark, a
published cross-language point). A hand-written scanner or a systems-language library like
`nom` is still faster, but grip is no longer an order of magnitude behind -- it is a
competitive combinator parser that keeps its grades and machine-checked soundness.

The `nom` parser used here is a byte-level leaf-counter matching grip's semantics
(validate, count leaves, keys not counted, `fold_many0` so no per-element `Vec`).

Update this file by running `lake exe bench` and `sh bench/mkchart.sh`.
