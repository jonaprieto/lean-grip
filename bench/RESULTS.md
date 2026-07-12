# grip benchmark results

Input: `bench/data/canada.json` (~2.1 MB, the standard nativejson-benchmark GeoJSON
file). Machine: Apple Silicon, arm64-darwin, on AC power. (Battery or Low Power Mode caps
the CPU frequency and inflates every figure by about 1.4x uniformly.) Toolchain:
`leanprover/lean4:v4.28.0`.

Methodology: best-of-20 wall time via `IO.monoNanosNow`, self-timed, all on the *same*
file and machine. grip and `Lean.Json` are timed by `lake exe bench` on that toolchain. The
lean4-parser number is its shipped `examples/JSON.lean` validator (fgdorais/lean4-parser,
toolchain v4.32.0-rc1) run through the same harness. grip's parser is `examples/Json.lean`,
built entirely from grip combinators (`fix`, `dispatch`, `seqR`, `alt`, `foldMany`,
`takeWhile1`), not a hand-rolled scanner.

The `~20ms` figures are the *pure parse*: input preloaded, timed between two `monoNanosNow`
calls, best of 20. For an end-to-end wall-clock cross-check, `sh bench/hyperfine.sh` runs
the built binary (`bench once`, a single parse then exit) under hyperfine, which reports
~46ms mean including process startup and the 2.1 MB file read. The two measurements answer
different questions, pure parse versus whole-command latency, and both are honest. The
tables below report the pure-parse number so grip and the other parsers are compared on the
same basis.

Read the `work` column before comparing. grip and lean4-parser validate the input (grip
also counts leaves, which is a cheap `Nat` add); `Lean.Json` builds a full DOM (a
`Lean.Json` tree), which is strictly more work.

| parser                        | parse_ms | work             | notes                                            |
|-------------------------------|---------:|------------------|--------------------------------------------------|
| grip (combinators)            |    ~20   | validate + count | byte-level; `examples/Json.lean`, pure combinators |
| Std.Internal.Parsec (core)    |    ~34   | validate + count | byte-level; Lean's std combinator library, same task |
| Lean.Json (core, built-in)    |    ~68   | full DOM build   | Lean's `Lean.Json.parse`; builds the tree        |
| lean4-parser (fgdorais)       |   ~273   | validate         | `SimpleParser String.Slice Char`; `sepBy` allocates |

The cleanest head-to-head is `Std.Internal.Parsec`, Lean's own standard combinator library:
byte-level, same toolchain, and the *same* validate-and-count task (it returns the identical
111130 leaf count). grip is about **1.7x faster** than it. Against the others: grip runs about
14x faster than lean4-parser on the competitor's own unmodified JSON example (a different
toolchain, v4.32.0-rc1), and about 3.5x faster than `Lean.Json`, which does more since it
builds a tree grip does not (treat that as context, not a head-to-head win). At ~20ms grip is
level with Haskell's attoparsec (see below). The `Std.Internal.Parsec` validator is in
`bench/Bench.lean`.

## First-byte dispatch

The JSON value parser used to be `alt keyword (alt number (alt string (alt array
object)))`. canada.json is about 99% numbers, so every value first failed a keyword scan,
a wasted sub-parse plus an error allocation, before it ever reached the number branch.
Replacing the `alt` chain with `GParser.dispatch` (peek the leading byte, jump straight to
the branch) removed that per-node waste and cut the parse from ~49ms to ~40ms, about 18%.

## Single-constructor result

The core result used to be `Except Err (α × Nat)`, so a successful step allocated an
`Except.ok` wrapping a `Prod`, two heap objects. Collapsing it to one constructor,
`ParseResult α = ok value offset | error e`, makes a success a single object and took the
parse from ~40ms to ~34ms, about 15%. Every combinator, the `cwit`/`ewit`/`swit` witnesses,
and the whole `grip-props` metatheory were ported to the new shape with no loss of features
and no new `sorry`.

## Specialize the scan loops

This was the largest single win. `scanFwd`/`foldFwd`/`natFwd` are the tight inner loops
that walk the bytes, and they were plain recursive `def`s, so their function arguments (the
byte predicate, the fold step) were closures called indirectly once per byte across the
whole 2 MB. Marking them `@[specialize]` (and `@[inline]` on the `weaken`/`weakenFallible`
wrappers) lets Lean monomorphize a statically-known predicate like `Ascii.isWs` straight
into the loop, so the per-byte call disappears. canada.json dropped from ~34ms to ~20ms,
about 40%.

An earlier draft of this file wrongly called this a "combinator indirection" wall and
claimed it needed a CPS or monomorphizing rewrite. It did not. A one-word attribute on the
three scan loops recovered most of the gap while leaving the combinator model intact. grip
is now level with attoparsec (~19.5ms) and about 1.5x off a hand-written Lean scanner.

## All example parsers

`lake exe bench` times every example parser, best-of-20 on the same machine. JSON runs on
canada.json and TOML on a real `Cargo.lock` (both vendored under `bench/data/`); the rest
run on inputs generated at startup. Throughput is input size over best time.

| parser | input                    | count  |  ms  | MB/s |
|--------|--------------------------|-------:|-----:|-----:|
| json   | canada.json, 2.1 MB      | 111130 | ~19  | ~110 |
| sexp   | 200 KB, 50k atoms        |  50000 | ~5.7 | ~35  |
| lambda | 100 KB application       |    ok  | ~3.7 | ~27  |
| http   | 80 KB, 10k headers       |  10000 | ~1.0 | ~80  |
| toml   | cargo.lock, 72 KB        |    307 | ~0.8 | ~89  |
| yaml   | 90 KB, 30k scalars       |  30001 | ~4.4 | ~20  |

`count` is the parser's own result on the input: leaf nodes for JSON, `[[package]]` tables
for TOML, list length for the others, and a success flag for `lambda`. These stress the
shared combinators (`fix`, `dispatch`, `capture`, `many`) across recursive, line-oriented,
and nested grammars. The TOML parser handles a genuine `Cargo.lock`, with comments,
`[[array-of-tables]]`, and multi-line arrays, rather than a synthetic input.

### Does the nom gap generalize past JSON?

Yes, and it narrowed after the scan-loop specialization. A `nom` S-expression atom-counter
on the same input grip's sexp bench uses (`"(" ++ "sym " * 50000 ++ ")"`, count 50000) runs
in ~0.7ms; grip's sexp is ~5.9ms, about 8x. JSON is about 10x (grip ~20ms, nom ~2ms). What
remains is the Lean-versus-Rust runtime floor: reference counting, bounds-checked indexing,
no borrowed slices. It is not the combinator model. (The `nom` parsers are not shipped;
there is no Rust in CI.)

## Where grip's time goes

The same leaf-count parse, several ways, on canada.json, best-of-20, on AC (all count
111130):

| approach                                   | parse_ms | note                                          |
|--------------------------------------------|---------:|-----------------------------------------------|
| Rust `nom` (byte-level, `fold_many0`)      |   ~2.0ms  | monomorphized, borrowed slices, no boxing     |
| hand-written Lean scanner (no combinators) |  ~13ms    | the Lean runtime floor                        |
| **grip today** (scan loops specialized)    |  ~20ms    | combinators; predicate monomorphized in-loop  |
| grip before `@[specialize]`                |  ~34ms    | scan predicate called indirectly per byte     |
| grip before single-constructor result      |  ~40ms    | two heap objects per step (`Except` + `Prod`) |

Reading the steps:

- `Except`+`Prod` to one constructor (~40 to ~34): a success now allocates one object.
- `@[specialize]` the scan loops (~34 to ~20): the per-byte predicate was the dominant
  cost, called indirectly once per byte. Monomorphizing it into the loop recovered that,
  with no CPS and no redesign; the combinator model stayed intact. An earlier draft called
  this a "combinator indirection wall" needing a rewrite, which was wrong; it was a one-word
  attribute.
- grip ~20 versus hand-written Lean ~13 (~1.5x): the residue is one `ParseResult` object per
  combinator step and the `GParser` struct and closure dispatch the specializer does not
  reach.
- hand-written Lean ~13 versus nom ~2: the Lean runtime floor (RC, bounds checks, no
  borrowed slices). That part is the language, not grip.

grip now sits level with Haskell's attoparsec (~19.5ms, DOM build, nativejson-benchmark, a
published cross-language point). A hand-written scanner or a systems-language library like
`nom` is still faster, but grip is no longer an order of magnitude behind. It is a
competitive combinator parser that keeps its grades and its machine-checked soundness.

The `nom` parser used here is a byte-level leaf-counter matching grip's semantics:
validate, count leaves, keys not counted, `fold_many0` so there is no per-element `Vec`.

Update this file by running `lake exe bench` and `sh bench/mkchart.sh`.
