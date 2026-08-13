# Changelog

## 0.3.2 — 2026-08-13

- Update the development doc-gen4 pin for Lean v4.33.0.

## 0.3.1 — 2026-08-12

- Adopt Lean v4.33.0 and precommit-lean v0.1.6.

Notable changes to grip. Format loosely follows
[Keep a Changelog](https://keepachangelog.com/en/1.1.0/); grip is pre-1.0, so breaking
changes to the core grade machinery can still happen between minor versions without
much ceremony beyond what's noted here.

## 0.3.0 — 2026-08-12

- Breaking: `GParser` gains a sixth field, `fwit`, proving that a failure reported from an
  in-bounds start offset carries a position between that offset and the end of the input.
  Parsers written with the combinator vocabulary are unaffected; code that constructs a
  `GParser` literal must now supply the proof.
- Document `Err.pos` and `ParseResult.error` against that contract. The position is proven
  in bounds; "furthest failure" and label completeness stay diagnostic conventions of the
  built-in combinators rather than obligations of the parser type.
- Define `GParser.fixFuel` through a private bounded approximation so the fuel recursion
  carries the failure-position invariant instead of discarding it. Its signature is unchanged.
- Add `consumptionWitness.le`: every consumption witness is monotone in the absolute offset.
- Prove the graded parser carrier equivalent to the primitive one in
  `GripProps.ParserTypeEquiv`, and classify which recursive paths are structural.

## 0.2.0 — 2026-08-07

- Move the JSON parser, corpus, properties, and benchmark to `lean-grip-json`; the core
  package keeps its non-JSON parser examples and benchmark.

## [Unreleased]

Everything below predates the first tag; recorded here as the proposed contents of the
first release, `v0.1.0`.

### Added

- The graded parser core: `GParser g α` indexed by a `Grade` (an `errors` x `consumes`
  pair of `Modality` values -- `never`/`possibly`/`always`), with an ungraded `Parser`
  alias (`GParser fallible α`) for callers who don't need the type-level guarantee.
  Backed by a flat `ByteArray → Nat → ParseResult α` `run` function plus five erased
  witness fields: `cwit`/`ewit`/`swit` prove the grade, `bwit` keeps successful offsets
  in bounds, and `fwit` keeps failure offsets between the parser's start and end of input.
- The consumption gate: `many`, `foldMany`, and `many1` demand an always-consuming
  (`conditional`) parser at the type level, so `many (pure x)` fails to elaborate instead
  of looping at runtime.
- Point combinators and scanners: `byte`, `ch`, `satisfy`, `takeWhile`/`takeWhile1`,
  `string`, `capture`, `captureWith?`, first-byte `dispatch`.
- `fix` for recursion: kernel-total via fuel set to the bytes remaining, with a runtime
  clamp forcing every recursive success to consume, so left recursion exhausts the fuel
  and fails rather than looping.
- `gdo`, graded do-notation, and the `Monad`/`Alternative`/`MonadExcept` instances for the
  ungraded `Parser`.
- Positioned errors with a caret, and `<?>` for attaching an expected-label.
- Expected-labels throughout `Grip.Json`, so a rejection names what the grammar wanted
  rather than reading `unexpected input`: leaf parsers carry `<?>` labels, `jstr`/`scanStr`
  name the specific string failure (bad escape, raw control byte, missing closing quote,
  invalid UTF-8), and `wsByte`/`containerBody` report the token they were looking for
  (`expected ':'`, `expected ',' or ']'`). `GParser.eof` is labelled too, so trailing
  garbage reads `expected end of input`.
- `Grip.Ascii` (named byte predicates/delimiter constants) and `Grip.Combinators` (the
  megaparsec-style vocabulary: `ws`, `digit`, `sepBy`, `between`, `manyTill`, `<?>`,
  `many1`, `endBy1`).
- `Grip.Json`: a value-producing (DOM) JSON parser and renderer -- `Json` inductive,
  `parse`/`parseString`, `render`/`toString` -- on top of the byte core. Numbers are exact
  `mantissa * 10^(-exponent)` (`Int`/`Nat`), never rounded through `Float`.
- `grip-props` (opt-in, pulls mathlib): the machine-checked metatheory. Graded-monad laws,
  grade soundness, `fix`'s fuel-completeness (`Guarded` bodies lose no accepted parse to
  the fuel bound), scanner correctness, and `GripProps.Container.parse_render`: parsing the
  rendering of any `Json` value returns that value, arrays and objects included. No
  `sorry`/`native_decide`; CI pins the theorem to exactly `propext`, `Classical.choice`,
  and `Quot.sound`.
- JSONTestSuite conformance gate (`lake exe conformance`), run against *both*
  `Grip.Examples.Json.json` (the grammar-strict validator) and `Grip.Json.parse` (the DOM
  parser `parse_render` is proved about), failing on disagreement between them on every
  non-`i_` (implementation-defined) file.
  `parsers/test_grip.sh` registers grip as a JSONTestSuite `parsers/` entry.
- Six worked example parsers under `examples/`: JSON (the RFC-8259 validator/benchmark),
  S-expressions, untyped lambda calculus, HTTP request line + headers, TOML, flow-style
  YAML.
- The benchmark suite (`bench/`): `lake exe bench` compares grip against
  `Std.Internal.Parsec`, a hand-written byte scanner, and Lean's own `Lean.Json`, plus a
  cross-language harness (`bench/cross-lang/`) against Rust `nom`, Haskell
  `attoparsec`/`megaparsec`, OCaml `angstrom`, and both an upstream and a local byte-ported
  `prim-parser`. `bench/run-all.sh` regenerates `bench/RESULTS.md`'s tables from a raw log.
- API docs generated by doc-gen4, published to GitHub Pages.

### Fixed

- Error positions inside `{..}`/`[..]` pointed at the opening bracket, or at a separator,
  instead of at the failure: `{"a": "b\qc"}` reported column 2 rather than column 9. The
  container body was `alt (bind elem ...) (pure #[])` followed by a closing-byte parser, so
  a failed first element was discarded by a fallback that succeeded, and `foldMany` (return
  grade `flexible`, never-errors) could not propagate a later element's failure at all.
  Both, plus the trailing closing-byte parser, are now one committed loop
  (`Grip.Json.containerBody`): in the tail a `,` obliges an element and its failure
  propagates; at the head the empty container is a fallback taken only when the element
  fails *and* the next non-whitespace byte is the closer, which no element can start with.
  Acceptance is unchanged across the whole JSONTestSuite corpus, and the DOM parser got
  faster (one fewer backtrack and closure per container).
  [#44](https://github.com/jonaprieto/lean-grip/issues/44).
- The JSONTestSuite conformance gate used to test only the grammar-strict validator, never
  the value-producing `Grip.Json.parse` the round-trip theorem is actually proved about --
  the two grammars share no code and had no equivalence check between them. The gate now
  runs both.
- Deep-nesting JSONTestSuite files used to crash the process (`fix` recurses on the Lean
  stack, not fuel); `parsers/test_grip.sh` and the CI conformance step now raise the
  process stack to its hard cap before running `lake exe conformance`, instead of
  excluding those files. Invoking the binary directly without a wrapper still needs the
  same `ulimit -s` bump.
- Invalid UTF-8 inside a JSON string body used to silently decode to an empty string via a
  Lean `panic!` in `String.fromUTF8!`; `Grip.Json.scanStr` now validates with the total
  `String.fromUTF8?` and rejects with a `ParseError` instead.
- `bench/run-all.sh`'s harness runner used to swallow a crashing harness's exit code
  (process substitution hid it from the `while` loop); it now captures output via command
  substitution and checks the exit status explicitly.
- `bench/cross-lang/prim-parser-upstream/BenchCanada.lean` printed an error on a wrong
  leaf count but still exited 0, and never printed a dataset name in its output (so the
  shell-level gate couldn't have caught a bad count either); it now exits nonzero on
  mismatch and carries the dataset name like every sibling harness.
- 78 pre-existing lines over the 100-column style-check limit in `grip-props/GripProps/Json/`.

### Known limitations

`parse_render` (`GripProps.Container`) is a round-trip proof on valid values only, and it
does constrain the production `Grip.Json.parse`/`render` it names -- but it says nothing
about the `.error` path, performance, or code the statement doesn't mention at all (like
the separate `Grip.Examples.Json` validator). Machine-checked means the stated theorems
hold, not that the library is bug-free.

The `.error` path is exercised by `#guard`s in `test/Test.lean` rather than by proof: the
positions, lines and labels reported for malformed input are pinned by tests, not by a
theorem. `alt`'s furthest-failure merge still only fires when both branches fail, and
`GParser.foldMany` still cannot propagate a failed repetition -- `Grip.Json` no longer
relies on either for its container bodies, but a client grammar built the same way would
hit the same loss.

[Unreleased]: https://github.com/jonaprieto/lean-grip/commits/main
