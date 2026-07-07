# grip

A fast, graded Lean 4 byte-parser library. grip aims to tie or beat attoparsec on
canada.json and beat `fgdorais/lean4-parser`, while adding grades as an opt-in
compile-time safety layer. `many (pure x)`, the classic infinite-loop footgun, is a
compile error.

[![CI](https://github.com/jonaprieto/grip/actions/workflows/ci.yml/badge.svg)](https://github.com/jonaprieto/grip/actions/workflows/ci.yml)
[![Lean](https://img.shields.io/badge/Lean-v4.28.0-blue)](lean-toolchain)
[![License](https://img.shields.io/badge/license-Apache--2.0-green)](LICENSE)

## Status

Milestone 0: skeleton. The parser core lands in Milestone 1.

## Benchmarks

Parsing canada.json (~2.1 MB). Chart and table land with the real core in Milestone 1.

## Packages

- `grip` (core, batteries only): the parser, grades, and erased soundness witnesses.
- `grip-props` (opt-in, grip + mathlib): the machine-checked metatheory.

## License

Apache-2.0.
