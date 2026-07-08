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
| grip (combinators)            |    ~40   | validate + count | byte-level; `examples/Json.lean`, pure combinators |
| Lean.Json (core, built-in)    |    ~68   | full DOM build   | Lean's `Lean.Json.parse`; builds the tree        |
| lean4-parser (fgdorais)       |   ~273   | validate         | `SimpleParser String.Slice Char`; `sepBy` allocates |

Apples-to-apples (both validate, no DOM): grip is about **6.8x faster than lean4-parser**
on the competitor's own unmodified JSON example. grip's validator is also ~1.7x faster
than `Lean.Json`, but that is not the same task -- `Lean.Json` materialises a tree grip
does not build, so treat it as context, not a like-for-like win.

## First-byte dispatch

The JSON value parser was `alt keyword (alt number (alt string (alt array object)))`. On
canada.json (~99% numbers) every value first *failed* a keyword scan -- a wasted
sub-parse plus an error allocation -- before reaching the number branch. Replacing the
`alt` chain with `GParser.dispatch` (peek the leading byte, jump straight to the branch)
removed that per-node waste and cut the parse from ~49ms to ~40ms (about 18%).

## All example parsers

`lake exe bench` times every example parser (JSON on canada.json, the rest on inputs
generated at startup), best-of-20 on the same machine. Throughput is input size over
best time.

| parser | input                | count  |  ms  | MB/s |
|--------|----------------------|-------:|-----:|-----:|
| json   | canada.json, 2.1 MB  | 111130 | ~40  | ~52  |
| sexp   | 200 KB, 50k atoms    |  50000 | ~9.0 | ~22  |
| lambda | 100 KB application   |    ok  | ~6.0 | ~17  |
| http   | 80 KB, 10k headers   |  10000 | ~1.5 | ~53  |
| toml   | 200 KB, 20k entries  |  20000 | ~7.1 | ~28  |
| yaml   | 90 KB, 30k scalars   |  30001 | ~7.3 | ~12  |

`count` is the parser's own result on the input (leaf nodes for JSON, list length for the
others; `lambda` reports a success flag). These stress the shared combinators (`fix`,
`dispatch`, `capture`, `many`) across recursive, line-oriented, and nested grammars.

## Cross-language reference (not run here)

Haskell's attoparsec parses canada.json in ~19.5ms in nativejson-benchmark (DOM build,
different language and runtime; a published number, not measured on this machine). It is
context for where a fast native parser sits, not a like-for-like grip comparison.

grip's open tuning target is `Except (α × Nat)`-per-step boxing in the combinator layer:
every combinator allocates a boxed result. An unboxed result encoding is the path to
closing that gap; the byte primitives themselves are already fast.

Update this file by running `lake exe bench` and `sh bench/mkchart.sh`.
