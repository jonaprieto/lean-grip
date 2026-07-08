# grip benchmark results

Input: `bench/data/canada.json` (~2.1 MB, the standard nativejson-benchmark GeoJSON
file). Machine: Apple Silicon, arm64-darwin. Toolchain: `leanprover/lean4:v4.28.0`.

Methodology: best-of-20 wall time via `IO.monoNanosNow`, self-timed. grip's number is
from `lake exe bench`. The lean4-parser number is its shipped `examples/JSON.lean`
validator (fgdorais/lean4-parser, toolchain v4.32.0-rc1) run through the *same*
best-of-20 harness on the *same* file and machine. Both do a full structural parse of
canada.json; grip additionally counts leaf nodes (cheap `Nat` adds). Neither builds a
materialised DOM, so these are not comparable to a DOM-building parser.

| parser                          | parse_ms | notes                                          |
|---------------------------------|---------:|------------------------------------------------|
| grip (combinators + dispatch)   |    ~40   | byte-level; `foldMany` (no list alloc); counts leaves |
| lean4-parser (fgdorais)         |   ~273   | `SimpleParser String.Slice Char`; `sepBy` builds arrays; validate-only |

grip parses canada.json about **6.8x faster** than lean4-parser's shipped validator. The
two engines differ (grip is byte-level; lean4-parser decodes to `Char` and its JSON
validator allocates via `sepBy`), but this is the competitor's own example, unmodified,
on identical input -- and grip wins decisively.

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

## Reference point

Haskell's attoparsec parses canada.json in ~19.5ms on comparable hardware
(nativejson-benchmark, DOM build). grip's combinator path is ~2x that. The remaining gap
is `Except (α × Nat)`-per-step boxing in the combinator layer -- a hand-rolled scan over
grip's own byte primitives reaches ~12.5ms. Reducing that boxing (an unboxed result
encoding) is the open tuning target; the byte primitives themselves are already fast.

Update this file by running `lake exe bench` and `sh bench/mkchart.sh`.
