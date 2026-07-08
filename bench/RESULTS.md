# grip benchmark results

Input: `bench/data/canada.json` (~2.1 MB, the standard nativejson-benchmark GeoJSON
file). Machine: Apple Silicon, arm64-darwin. Toolchain: `leanprover/lean4:v4.28.0`.

Methodology: best-of-20 wall time via `IO.monoNanosNow`, self-timed in `lake exe bench`.
What is measured is structural validation plus a leaf-node count (each number, string,
`true`/`false`/`null` counts 1; arrays and objects sum their children). It is NOT the
construction of a materialised value tree, so these numbers are not directly comparable
to a DOM-building parser such as attoparsec.

| parser                         | parse_ms | notes                                   |
|--------------------------------|---------:|-----------------------------------------|
| grip (combinators + fix)       |    ~49   | the ergonomic combinator path; sole benchmark |
| attoparsec (reference)         |    ~19.5 | nativejson-benchmark, DOM build, not run here |

The combinator path is about 2.5x the attoparsec reference. The dominant cost is
`GParser.fix` rebuilding the combinator tree on each recursive entry and the `Except`
boxing at every combinator step. grip's byte primitives themselves are fast; the
overhead sits in the `fix` and combinator layer, not the core. A build-once fixpoint
encoding and reduced boxing are the open tuning targets.

Update this file by running `lake exe bench` and `sh bench/mkchart.sh`.
