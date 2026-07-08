# grip

A graded Lean 4 byte-parser library. grip pairs a fast `ByteArray` core with grades:
an opt-in, compile-time layer that tracks whether a parser may error and whether it
must consume input. The headline payoff is that `many (pure x)`, the classic
parsec/attoparsec infinite-loop footgun, is a **compile error**.

[![CI](https://github.com/jonaprieto/grip/actions/workflows/ci.yml/badge.svg)](https://github.com/jonaprieto/grip/actions/workflows/ci.yml)
[![Lean](https://img.shields.io/badge/Lean-v4.28.0-blue)](lean-toolchain)
[![License](https://img.shields.io/badge/license-Apache--2.0-green)](LICENSE)
[![canada.json](https://img.shields.io/badge/canada.json-~49ms%20(combinators)-blue)](bench/RESULTS.md)

## Status

Milestone 1: the core is in. Byte primitives, the `Parser`/graded `GParser` split with
`Monad`/`Alternative`/`MonadExcept`, `gdo`, the always-consume `many` gate, `fix` for
recursion, positioned `ParseError` with labels and caret, and a combinator JSON example
wired to the canada.json benchmark. The machine-checked metatheory (`grip-props`) and
Verso docs are later milestones.

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

## Benchmarks

Parsing canada.json (~2.1 MB, standard nativejson-benchmark GeoJSON), best-of-20,
self-timed. The benchmark measures structural validation plus a leaf-node count, not
construction of a materialised value tree, so it is not directly comparable to a
DOM-building parser like attoparsec. See [bench/RESULTS.md](bench/RESULTS.md).

![canada.json parse time](bench/results.svg)

The ergonomic combinator path is about 2.5x the attoparsec reference. The cost is in the
combinator layer, not the core: `GParser.fix` rebuilds the combinator tree on each
recursive entry and every step boxes through `Except`. A build-once fixpoint and reduced
boxing are the open tuning targets. Regenerate with `lake exe bench` and
`sh bench/mkchart.sh`.

## Packages

- `grip` (core, batteries only): the parser, grades, and erased soundness witnesses.
  Depend on this and you never transitively acquire mathlib.
- `grip-props` (opt-in, grip + mathlib): the machine-checked metatheory.

## License

Apache-2.0.
