# grip

A graded Lean 4 byte-parser library. grip pairs a fast `ByteArray` core with grades:
an opt-in, compile-time layer that tracks whether a parser may error and whether it
must consume input. The headline payoff is that `many (pure x)`, the classic
parsec/attoparsec infinite-loop footgun, is a **compile error**.

[![CI](https://github.com/jonaprieto/grip/actions/workflows/ci.yml/badge.svg)](https://github.com/jonaprieto/grip/actions/workflows/ci.yml)
[![Lean](https://img.shields.io/badge/Lean-v4.28.0-blue)](lean-toolchain)
[![License](https://img.shields.io/badge/license-Apache--2.0-green)](LICENSE)
[![canada.json](https://img.shields.io/badge/canada.json-~20ms%20(14x%20vs%20lean4--parser)-blue)](bench/RESULTS.md)

## Status

The core is in. Byte primitives, the `Parser`/graded `GParser` split with
`Monad`/`Alternative`/`MonadExcept`, `gdo`, the always-consume `many` gate, `fix` for
recursion, first-byte `dispatch`, `capture` for building syntax trees, and positioned
`ParseError` with labels and caret. The machine-checked metatheory lives in `grip-props`;
Verso docs are a later milestone.

Two batteries-only helper modules sit on top: `Grip.Ascii` (named byte predicates
`isWs`/`isDigit`/`isHexDigit`/..., delimiter constants `quote`/`comma`/`lbrace`/..., and
`code : Char → UInt8`) and `Grip.Combinators` (the megaparsec-style vocabulary: `ws`,
`digit`, `oneOf`, `sepBy`, `between`, `option`, `choice`, `manyTill`, `notFollowedBy`, ...
plus the familiar operators `<$> <*> *> <* <|>` at the graded level, and `<?>` for
labels). `import Grip` brings them all in.

Worked example parsers under [`examples/`](examples/), each with `#guard` tests: JSON
(byte-level, benchmarked), S-expressions, untyped lambda calculus, HTTP request lines +
headers, a TOML scalar subset, and flow-style YAML.

## Quick start

Add grip to your `lakefile.toml`:

```toml
[[require]]
name = "grip"
git = "https://github.com/jonaprieto/grip"
rev = "main"
```

A parser is a `GParser g α` (graded) or the ungraded `Parser α`. Combinators run over a
`ByteArray`; `run?` returns `Option`, `parse` returns a positioned `ParseError`:

```lean
import Grip
open Grip

-- A run of one or more digits; the result is the count of bytes consumed.
-- `conditional` = always consumes on success, may error.
def digits : GParser conditional Nat :=
  GParser.takeWhile1 (fun b => 48 ≤ b && b ≤ 57)

#eval GParser.run? digits "2026".toUTF8   -- some 4
#eval GParser.run? digits "x".toUTF8      -- none
```

Grades are opt-in. Write at the ungraded `Parser` with `Monad`/`Alternative`/`do` (or
`gdo` to keep grades precise) and still get the compile-time consumption gate below.

## The gate

The one grade payoff to remember: `many`, `foldMany`, and `some` demand an
always-consuming parser at the type level. `pure x` never consumes, so:

```lean
def loop : Parser Unit := many (pure ())   -- compile error: many needs an always-consuming parser
```

You do not opt into this safety; it is carried by the library's own combinator types. A
user writes at the ungraded `Parser` and still gets it. Writing a precise grade
(`GParser conditional α`) is how you export a machine-checked contract to downstream
combinators.

## Examples

Six worked parsers under [`examples/`](examples/), each with `#guard` tests that run in
CI:

| file | grammar |
|------|---------|
| [Json.lean](examples/Json.lean)     | byte-level JSON (the benchmark)  |
| [Sexp.lean](examples/Sexp.lean)     | S-expressions                    |
| [Lambda.lean](examples/Lambda.lean) | untyped lambda calculus          |
| [Http.lean](examples/Http.lean)     | HTTP request line + headers      |
| [Toml.lean](examples/Toml.lean)     | a TOML scalar subset             |
| [Yaml.lean](examples/Yaml.lean)     | flow-style YAML                  |

They share a shape: `fix` for recursion, `dispatch` to pick a branch on the leading byte,
`capture` to pull out a token, and `many`/`foldMany` for repetition. The S-expression
core is the whole idea in five lines:

```lean
def sexp : GParser conditional Sexp :=
  GParser.fix fun sexp =>
    let atom := Sexp.atom <$> GParser.capture (GParser.takeWhile1 isAtomByte)
    let list := GParser.byteC '(' *> GParser.ws *>
      ((Sexp.list <$> GParser.many (sexp <* GParser.ws)) <* (GParser.ws *> GParser.byteC ')'))
    GParser.ws *> GParser.dispatch fun b => if b == Ascii.lparen then list else atom
```

## When to reach for grip

grip is a parser-combinator library: composable, readable grammars with a compile-time
consumption guarantee (the [gate](#the-gate)) and machine-checked soundness. It is also
fast -- on canada.json it is level with Haskell's attoparsec (~20ms) and ~1.5x off a
hand-written Lean byte scanner (~13ms), so you rarely pay for the ergonomics. A bespoke
hand-written scanner or a systems-language library like Rust's `nom` (~2ms) is still
faster on raw throughput; reach for one of those only when the last few milliseconds beat
grammar clarity and the many-gate safety.

## Benchmarks

Parsing canada.json (~2.1 MB, standard nativejson-benchmark GeoJSON), best-of-20,
self-timed, all on the same file and machine. grip's parser is
[`examples/Json.lean`](examples/Json.lean), built entirely from grip combinators (`fix`,
`dispatch`, `seqR`, `alt`, `foldMany`, `takeWhile1`), not a hand-rolled scanner.

![canada.json parse time](bench/results.svg)

Apples-to-apples, both validating, grip is about **14x faster than lean4-parser**
(grip ~20ms, lean4-parser ~273ms) and ~3.5x faster than Lean's built-in `Lean.Json.parse`
(~68ms, which does more -- it builds a full DOM). At ~20ms grip is level with Haskell's
attoparsec (~19.5ms).

`bench/RESULTS.md` walks the path from ~49ms to ~20ms: first-byte `dispatch` (~49→40),
the single-constructor `ParseResult` (~40→34), and `@[specialize]` on the byte-scan loops
so a known predicate is monomorphized in-loop instead of called per byte (~34→20, the big
one). What remains is the Lean runtime floor: a hand-written Lean scanner does ~13ms and
Rust's `nom` ~2ms. See [bench/RESULTS.md](bench/RESULTS.md); regenerate with `lake exe bench` and
`sh bench/mkchart.sh`.

## Packages

- `grip` (core, batteries only): the parser, grades, and erased soundness witnesses.
  Depend on this and you never transitively acquire mathlib.
- `grip-props` (opt-in, grip + mathlib): the machine-checked metatheory.

## Acknowledgements

grip took its central idea from
[prim-parser](https://github.com/janmasrovira/prim-parser) by Jan Mas Rovira: a
**`Necessity`-graded monad**, where each parser's type records whether it may error and
whether it consumes input, and sequencing/choice combine those grades. That graded
discipline (and the many-gate it enables) is prim-parser's contribution. grip carries it
onto its own byte-level `ByteArray` core with erased soundness witnesses, and adds the
`ParseResult` result, first-byte `dispatch`, and the `@[specialize]` scan loops.

## License

Apache-2.0.
