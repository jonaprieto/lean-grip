# grip

[![CI](https://github.com/jonaprieto/lean-grip/actions/workflows/ci.yml/badge.svg)](https://github.com/jonaprieto/lean-grip/actions/workflows/ci.yml)
[![Release](https://img.shields.io/github/v/release/jonaprieto/lean-grip?display_name=tag&sort=semver)](https://github.com/jonaprieto/lean-grip/releases)
[![Lean 4](https://img.shields.io/badge/Lean%204-v4.33.0-6f42c1)](lean-toolchain)
[![Docs](https://img.shields.io/badge/docs-GitHub%20Pages-4c8bf5)](https://jonaprieto.github.io/lean-grip/)
[![License](https://img.shields.io/badge/license-Apache--2.0-green)](LICENSE)

Graded byte parsers for Lean 4. Parsers consume `ByteArray`; grades record failure and input
consumption. Repetition requires an always-consuming parser, so `many (pure x)` is rejected by
the type checker. Erased witnesses also keep every reported success or failure offset within the
input interval reached from the parser's starting position.

The core package is Mathlib-free: its only runtime dependency is Batteries. The optional
`grip-props/` proof project imports Mathlib for the machine-checked law suite and is not part of a
normal `require grip` dependency closure.

API documentation: <https://jonaprieto.github.io/lean-grip/>.

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

[`tptp`](https://github.com/jonaprieto/lean-grip-tptp) uses Grip for TPTP/TSTP parsing.

## License

Apache-2.0.
