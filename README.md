# lean-grip

[![CI](https://github.com/jonaprieto/lean-grip/actions/workflows/ci.yml/badge.svg)](https://github.com/jonaprieto/lean-grip/actions/workflows/ci.yml)
[![Release](https://img.shields.io/github/v/release/jonaprieto/lean-grip?display_name=tag&sort=semver)](https://github.com/jonaprieto/lean-grip/releases)
[![Lean 4](https://img.shields.io/badge/Lean%204-v4.33.1-6f42c1)](lean-toolchain)
[![Docs](https://img.shields.io/badge/docs-GitHub%20Pages-4c8bf5)](https://jonaprieto.github.io/lean-grip/)
[![License](https://img.shields.io/badge/license-Apache--2.0-green)](LICENSE)

Graded byte parsers for Lean 4. Parsers consume `ByteArray`; grades record failure and input
consumption. Repetition requires an always-consuming parser, so `many (pure x)` is rejected by
the type checker. Erased witnesses also keep every reported success or failure offset within the
input interval reached from the parser's starting position.

The core package is Mathlib-free: its only runtime dependency is Batteries. The optional
`grip-props/` proof project imports Mathlib for the machine-checked law suite and is not part of a
normal `require grip` dependency closure.

## Problem

Recursive byte parsers need a way to rule out non-consuming repetition and keep reported offsets
within the input that was actually parsed.

API documentation: <https://jonaprieto.github.io/lean-grip/>.

## Development

This project is maintained by its author with AI-assisted development tools.
Changes are reviewed, tested, and remain the maintainer's responsibility.

## Quick start

```lean
import Grip
open Grip GParser

def point : Parser (Nat × Nat) := do
  ch '('
  let x ← nat
  ch ','
  let y ← nat
  ch ')'
  return (x, y)

#eval run? point "(3,14)".toUTF8
```

The graded API uses `GParser`, `gdo`, `fix`, `dispatch`, `capture`, and `many`. `ParseError.pretty`
provides a dependency-free fallback; [`grip-diagnostics`](https://github.com/jonaprieto/lean-grip-diagnostics)
adds source context and styled output.

## Verification

`grip-props` contains the optional machine-checked laws. Core parser benchmarks are recorded in
[`bench/RESULTS.md`](bench/RESULTS.md); JSON conformance and DOM benchmarks live in
[`grip-json`](https://github.com/jonaprieto/lean-grip-json).

```sh
lake build
lake exe bench
```

## Related projects

[`tptp`](https://github.com/jonaprieto/lean-grip-tptp) uses Grip for TPTP/TSTP parsing;
[`lean-argus`](https://github.com/jonaprieto/lean-argus),
[`lean-calc-chat`](https://github.com/jonaprieto/lean-calc-chat), and
[`oatp`](https://github.com/jonaprieto/oatp) build on the parser.

## Acknowledgements

Grip took its inspiration from [prim-parser](https://github.com/janmasrovira/prim-parser) by Jan
Mas Rovira. It diverges by encoding parser behavior at the type level: grades track failure and
input consumption, making repetition safe by construction. Grip also uses a byte-level core,
`ParseResult`, first-byte `dispatch`, and `@[specialize]` scan loops.

## License

Apache-2.0.
