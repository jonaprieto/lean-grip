# grip

A graded Lean 4 byte-parser library. grip pairs a fast `ByteArray` core with grades:
an opt-in, compile-time layer that tracks whether a parser may error and whether it
must consume input. The headline payoff is that `many (pure x)`, the classic
parsec/attoparsec infinite-loop footgun, is a **compile error**.

[![CI](https://github.com/jonaprieto/grip/actions/workflows/ci.yml/badge.svg)](https://github.com/jonaprieto/grip/actions/workflows/ci.yml)
[![Lean](https://img.shields.io/badge/Lean-v4.28.0-blue)](lean-toolchain)
[![License](https://img.shields.io/badge/license-Apache--2.0-green)](LICENSE)
[![canada.json](https://img.shields.io/badge/canada.json-~40ms%20(6.8x%20vs%20lean4--parser)-blue)](bench/RESULTS.md)

## Status

The core is in. Byte primitives, the `Parser`/graded `GParser` split with
`Monad`/`Alternative`/`MonadExcept`, `gdo`, the always-consume `many` gate, `fix` for
recursion, first-byte `dispatch`, `capture` for building syntax trees, and positioned
`ParseError` with labels and caret. The machine-checked metatheory lives in `grip-props`;
Verso docs are a later milestone.

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
    let atom := GParser.map Sexp.atom (GParser.capture (GParser.takeWhile1 isAtomByte))
    let list := GParser.seqR (GParser.byte 40)              -- '('
      (GParser.seqR ws (GParser.seqL (GParser.map Sexp.list
        (GParser.many (GParser.seqL sexp ws))) (GParser.byte 41)))  -- ')'
    GParser.seqR ws (GParser.dispatch fun b => if b == 40 then list else atom)
```

## Benchmarks

Parsing canada.json (~2.1 MB, standard nativejson-benchmark GeoJSON), best-of-20,
self-timed. grip's combinator JSON parser runs about **6.8x faster than lean4-parser's
shipped JSON validator** on the same file and machine (grip ~40ms, lean4-parser ~273ms).
Both do a full structural parse; grip is byte-level where lean4-parser decodes to `Char`.
See [bench/RESULTS.md](bench/RESULTS.md).

![canada.json parse time](bench/results.svg)

Against Haskell's attoparsec (~19.5ms, DOM build) grip's combinator path is ~2x slower;
the gap is `Except`-per-step boxing in the combinator layer, not the byte core (a
hand-rolled scan over grip's primitives reaches ~12.5ms). Reducing that boxing is the
open tuning target. First-byte `dispatch` -- jumping to a branch on the leading byte
instead of trying an `alt` chain -- already cut ~18% off the JSON parse. Regenerate with
`lake exe bench` and `sh bench/mkchart.sh`.

## Packages

- `grip` (core, batteries only): the parser, grades, and erased soundness witnesses.
  Depend on this and you never transitively acquire mathlib.
- `grip-props` (opt-in, grip + mathlib): the machine-checked metatheory.

## License

Apache-2.0.
