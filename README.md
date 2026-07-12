# grip

A graded byte-parser library for Lean 4. The core parses over a raw `ByteArray`. On top
of it sits an optional grade layer that records, at compile time, whether a parser can
fail and whether it always consumes input. One thing that layer buys you: `many (pure x)`
does not compile. That expression loops forever at runtime in parsec and attoparsec; here
the type checker rejects it up front.

[![CI](https://github.com/jonaprieto/grip/actions/workflows/ci.yml/badge.svg)](https://github.com/jonaprieto/grip/actions/workflows/ci.yml)
[![Lean](https://img.shields.io/badge/Lean-v4.28.0-blue)](lean-toolchain)
[![License](https://img.shields.io/badge/license-Apache--2.0-green)](LICENSE)
[![canada.json](https://img.shields.io/badge/canada.json-~20ms%20(14x%20vs%20lean4--parser)-blue)](bench/RESULTS.md)

## Status

The core is in. That means the byte primitives, the `Parser`/graded `GParser` split with
`Monad`/`Alternative`/`MonadExcept`, `gdo`, the always-consume `many` gate, `fix` for
recursion, first-byte `dispatch`, `capture` for building syntax trees, and a positioned
`ParseError` with labels and a caret. The machine-checked metatheory lives in `grip-props`.
Verso docs are a later milestone.

Two batteries-only helper modules sit on top. `Grip.Ascii` gives you named byte
predicates (`isWs`, `isDigit`, `isHexDigit`, ...), delimiter constants (`quote`, `comma`,
`lbrace`, ...), and `code : Char → UInt8`. `Grip.Combinators` gives you the megaparsec-style
vocabulary: `ws`, `digit`, `oneOf`, `sepBy`, `between`, `option`, `choice`, `manyTill`,
`notFollowedBy`, and the rest, plus the familiar `<$> <*> *> <* <|>` operators at the graded
level and `<?>` for labels. `import Grip` pulls in all of it.

There are worked example parsers under [`examples/`](examples/), each with its own `#guard`
tests: JSON (byte-level, the one we benchmark), S-expressions, untyped lambda calculus,
HTTP request lines and headers, TOML (tables, arrays, comments, and it parses a real
`Cargo.lock`), and flow-style YAML.

## Quick start

Add grip to your `lakefile.toml`:

```toml
[[require]]
name = "grip"
git = "https://github.com/jonaprieto/grip"
rev = "main"
```

A parser is a `GParser g α` (graded) or the ungraded `Parser α`. Combinators run over a
`ByteArray`. `run?` gives you back an `Option`; `parse` gives you a positioned
`ParseError`:

```lean
import Grip
open Grip

-- A run of one or more digits; the result is the count of bytes consumed.
-- `conditional` = always consumes on success, may error. `Ascii.isDigit` is a
-- named byte predicate from `Grip.Ascii` -- no magic `48 ≤ b && b ≤ 57` literals.
def digits : GParser conditional Nat :=
  GParser.takeWhile1 Ascii.isDigit

#eval GParser.run? digits "2026".toUTF8   -- some 4
#eval GParser.run? digits "x".toUTF8      -- none

-- Or lean on `Grip.Combinators` directly: `digit` is the byte parser, and the
-- operators/vocabulary compose it -- e.g. `ws *> digit` skips leading spaces.
```

The example parsers use these facilities throughout rather than hand-rolled byte math:
the `Ascii` predicates and constants (`isWs`, `isHexDigit`, `quote`, `lbrace`), the
`Combinators` (`ws`, `sepBy`, `between`, `choice`), and the operators (`<$> <*> *> <* <|>`).

Grades are opt-in. You can write at the ungraded `Parser` with `Monad`/`Alternative`/`do`
(or reach for `gdo` when you want to keep grades precise) and still get the compile-time
consumption gate described below.

## The gate

Here is the one grade payoff worth remembering. `many`, `foldMany`, and `some` all demand
an always-consuming parser at the type level. `pure x` never consumes, so this fails to
elaborate:

```lean
def loop : Parser Unit := many (pure ())   -- compile error: many needs an always-consuming parser
```

You never opt into this safety. It rides on the library's own combinator types, so a user
who writes at the ungraded `Parser` still gets it. Writing a precise grade
(`GParser conditional α`) is how you export a machine-checked contract to downstream
combinators.

## Total, verified combinators

grip's whole combinator core is total, not `partial` -- recursion included. `many`,
`foldMany`, and the `foldFwd`/`scanFwd`/`natFwd` loops underneath them are structural on
`arr.size - q`, and the [gate](#the-gate) forces every repeated element to be
always-consuming (grade `⟨_, always⟩`), which is exactly the "the input shrank" fact a
termination proof needs, enforced at the type level. `fix`, the one recursive knot, is
total too: it recurses on a fuel set to the bytes remaining, and its runtime clamp forces
every recursive success to consume, so that fuel provably suffices for any guarded grammar
(a left-recursive body exhausts it and fails, rather than looping). Nothing on the hot path
is an opaque axiom, so the `grip-props` metatheory can reason about every combinator,
recursion and all.

That is a deliberate trade. grip is concrete over an in-memory `ByteArray`, which is
finite, so `arr.size - q` is a free well-founded measure -- and the same finiteness bounds
`fix`'s fuel. It is not generic over arbitrary streams. A stream-generic library gets you
sockets and pipes, but pays for them with `partial` fold and fixpoint combinators that no
theorem can unfold, since a `partial def` is opaque to the kernel. grip stakes out the
other corner (total, verified, byte-level) where the generic libraries sit at generic and
partial. That makes it a different point on the tradeoff curve, not a drop-in replacement.
Reach for grip when you parse bytes in memory and want the proofs.

## Examples

Six worked parsers live under [`examples/`](examples/), each with `#guard` tests that run
in CI:

| file | grammar |
|------|---------|
| [Json.lean](examples/Json.lean)     | byte-level JSON (the benchmark)  |
| [Sexp.lean](examples/Sexp.lean)     | S-expressions                    |
| [Lambda.lean](examples/Lambda.lean) | untyped lambda calculus          |
| [Http.lean](examples/Http.lean)     | HTTP request line + headers      |
| [Toml.lean](examples/Toml.lean)     | TOML (tables, arrays, comments)  |
| [Yaml.lean](examples/Yaml.lean)     | flow-style YAML                  |

They all share a shape: `fix` for recursion, `dispatch` to pick a branch on the leading
byte, `capture` to pull out a token, and `many`/`foldMany` for repetition. The
S-expression core is the whole idea in five lines:

```lean
def sexp : GParser conditional Sexp :=
  GParser.fix fun sexp =>
    let atom := Sexp.atom <$> GParser.capture (GParser.takeWhile1 isAtomByte)
    let list := GParser.byteC '(' *> GParser.ws *>
      ((Sexp.list <$> GParser.many (sexp <* GParser.ws)) <* (GParser.ws *> GParser.byteC ')'))
    GParser.ws *> GParser.dispatch fun b => if b == Ascii.lparen then list else atom
```

## When to reach for grip

grip is a parser-combinator library: composable grammars that read clearly, with a
compile-time consumption guarantee (the [gate](#the-gate)) and machine-checked soundness.
It is also fast. On canada.json it runs level with Haskell's attoparsec and within about
1.5x of a hand-written Lean byte scanner, so the ergonomics rarely cost you anything. A
bespoke scanner or a systems-language library like Rust's `nom` will still beat it on raw
throughput; go there when the last few milliseconds matter more than grammar clarity and
the many-gate safety. The numbers are in [bench/RESULTS.md](bench/RESULTS.md).

## Benchmarks

Parsing canada.json (~2.1 MB, the standard nativejson-benchmark GeoJSON file), best-of-20,
self-timed. grip's parser is [`examples/Json.lean`](examples/Json.lean), built entirely
from grip combinators (`fix`, `dispatch`, `foldMany`, `takeWhile1`), not a hand-rolled
scanner.

![canada.json parse time](bench/results.svg)

Both validating, grip comes in roughly 14x faster than lean4-parser and lands next to
Haskell's attoparsec. The exact numbers, the methodology, the optimization path, and the
cross-language comparison (`Lean.Json`, Rust's `nom`, a hand-written Lean scanner) all live
in [bench/RESULTS.md](bench/RESULTS.md), which is the single source of truth. Regenerate
them with `lake exe bench` and `sh bench/mkchart.sh`.

## Packages

- `grip` (core, batteries only): the parser, the grades, and the erased soundness
  witnesses. Depend on this and you never transitively pull in mathlib.
- `grip-props` (opt-in, grip + mathlib): the machine-checked metatheory.

## Acknowledgements

grip took its central idea from
[prim-parser](https://github.com/janmasrovira/prim-parser) by Jan Mas Rovira: a
`Necessity`-graded monad, where each parser's type records whether it may error and whether
it consumes input, and sequencing and choice combine those grades. That graded discipline,
and the many-gate it enables, is prim-parser's contribution. grip carries it onto its own
byte-level `ByteArray` core with erased soundness witnesses, and adds the `ParseResult`
result type, first-byte `dispatch`, and the `@[specialize]` scan loops.

## License

Apache-2.0.
