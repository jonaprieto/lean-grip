/-
Copyright 2026 Jonathan Cubides. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Grip.Parser

/-!
# Grip.Examples.Json -- byte-level JSON parser built on grip combinators

Parses a JSON value and returns the count of JSON leaf-value nodes in its tree:
each number, string, `true`/`false`/`null` contributes 1; arrays and objects
contribute the sum of their element counts (the container itself adds nothing).

canada.json (GeoJSON, ~2.1 MB) uses floating-point coordinates (`-65.613033`).
The number scanner accepts sign, decimal point, and exponent characters,
covering all JSON number forms.

## Design

This parser is written entirely from grip combinators. The leaf parsers
(`ws`, `keyword`, `number`, `jstring`) are graded combinators; the recursive
`value` is `GParser.fix`, and the array and object repetitions are `foldMany`
over an always-consuming `", element"` parser (the comma forces consumption, so
the many-gate accepts it). No hand-rolled byte recursion.

Recursion uses grip's `fix`, which is `partial` under the hood (grip has no
kernel-total, size-indexed fix); see the `fix` note in `Grip/Graded.lean`. The
benchmark measures structural validation plus a leaf-node count, not the
construction of a materialised value tree, so its timing is not directly
comparable to a DOM-building parser.
-/

namespace Grip.Examples.Json

open Grip

-- Byte predicates -------------------------------------------------------

/-- JSON insignificant whitespace. -/
@[inline] private def isWs (b : UInt8) : Bool :=
  b == 32 || b == 10 || b == 9 || b == 13

/-- Characters that may appear in a JSON number token (digits, sign, dot, exponent). -/
@[inline] private def isNumCh (b : UInt8) : Bool :=
  (48 ≤ b && b ≤ 57) || b == 46 || b == 45 || b == 43 || b == 101 || b == 69

/-- ASCII letters, for the keywords `true`, `false`, `null`. -/
@[inline] private def isAlpha (b : UInt8) : Bool :=
  (97 ≤ b && b ≤ 122) || (65 ≤ b && b ≤ 90)

-- Grip combinator leaf parsers -------------------------------------------

/-- Skip insignificant whitespace. Grade `flexible` (never errors, possibly consumes). -/
@[inline] private def ws : GParser flexible Nat := GParser.takeWhile isWs

/-- A keyword (`true`/`false`/`null`) as an ASCII-letter run. Leaf count 1. `conditional`. -/
@[inline] private def keyword : GParser conditional Nat :=
  GParser.map (fun _ => 1) (GParser.takeWhile1 isAlpha)

/-- A number token (a run of number characters). Leaf count 1. `conditional`. -/
@[inline] private def number : GParser conditional Nat :=
  GParser.map (fun _ => 1) (GParser.takeWhile1 isNumCh)

/-- A string `"..."` (escape-transparent scan to the closing quote). Leaf count 1. `conditional`. -/
@[inline] private def jstring : GParser conditional Nat :=
  GParser.seqR (GParser.byte 34)                      -- opening '"'
    (GParser.seqR (GParser.takeWhile (· != 34))        -- content bytes
      (GParser.map (fun _ => 1) (GParser.byte 34)))    -- closing '"', count 1

-- Recursive value via `fix` ---------------------------------------------

/-- Parse one JSON value (after any leading whitespace), returning its leaf count.
Arrays and objects are folded with `foldMany` over an always-consuming element. -/
private def value : GParser conditional Nat :=
  GParser.fix fun value =>
    -- ", value" element for arrays: the comma makes it always-consuming.
    let commaValue : GParser conditional Nat :=
      GParser.seqR ws (GParser.seqR (GParser.byte 44) (GParser.seqR ws value))
    let arrayBody : GParser flexible Nat :=
      GParser.alt
        (GParser.map2 (· + ·) value (GParser.foldMany (· + ·) 0 commaValue))
        (GParser.pure 0)
    let array : GParser conditional Nat :=
      GParser.seqR (GParser.byte 91)                    -- '['
        (GParser.seqR ws
          (GParser.seqL arrayBody (GParser.seqR ws (GParser.byte 93))))  -- ']'
    -- "key" : value member, returning the value's leaf count.
    let pair : GParser conditional Nat :=
      GParser.seqR jstring
        (GParser.seqR ws (GParser.seqR (GParser.byte 58) (GParser.seqR ws value)))
    let commaPair : GParser conditional Nat :=
      GParser.seqR ws (GParser.seqR (GParser.byte 44) (GParser.seqR ws pair))
    let objectBody : GParser flexible Nat :=
      GParser.alt
        (GParser.map2 (· + ·) pair (GParser.foldMany (· + ·) 0 commaPair))
        (GParser.pure 0)
    let object : GParser conditional Nat :=
      GParser.seqR (GParser.byte 123)                   -- '{'
        (GParser.seqR ws
          (GParser.seqL objectBody (GParser.seqR ws (GParser.byte 125))))  -- '}'
    GParser.seqR ws
      (GParser.alt keyword
        (GParser.alt number
          (GParser.alt jstring
            (GParser.alt array object))))

/-- Parse one complete JSON value from `arr`; return the total leaf count.
Leaf semantics: 1 per number, string, or keyword; sum of children for arrays and
objects (containers do not add 1 themselves). Grade `fallible` (the `Parser` face). -/
def json : Parser Nat := GParser.weakenFallible value

-- Acceptance guards -------------------------------------------------------

-- count 5: [1,-2.5e3,true,null] is 4 leaves, "x" is 1; keys are not counted.
#guard (GParser.run? json "{\"a\":[1,-2.5e3,true,null],\"b\":\"x\"}".toUTF8) == some 5

-- Malformed input (missing value before `}`): rejected.
#guard (GParser.run? json "{\"a\":}".toUTF8) == none

end Grip.Examples.Json
