# grip

[![CI](https://github.com/jonaprieto/lean-grip/actions/workflows/ci.yml/badge.svg)](https://github.com/jonaprieto/lean-grip/actions/workflows/ci.yml)
[![Lean 4](https://img.shields.io/badge/Lean%204-library-5f5f5f)](lean-toolchain)
[![License](https://img.shields.io/badge/license-Apache--2.0-green)](LICENSE)

Graded byte parsers for Lean 4. Parsers consume `ByteArray`; grades record failure and input
consumption. Repetition requires an always-consuming parser, so `many (pure x)` is rejected by
the type checker.

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

`grip-props` contains the optional machine-checked laws. The JSON example is checked against the
JSONTestSuite corpus, and benchmarks are recorded in [`bench/RESULTS.md`](bench/RESULTS.md).

```sh
lake build
bash tools/run-conformance.sh
```

## Related projects

[`tptp`](https://github.com/jonaprieto/lean-tptp) uses Grip for TPTP/TSTP parsing.

## License

Apache-2.0.
