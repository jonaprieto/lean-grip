/-
Copyright (c) 2026 Jonathan Cubides. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Prieto-Cubides
-/
import Grip
import Test.Modality
import Test.Grade
import Test.Error
import Test.Byte
import Test.Char
import Test.Ascii
import Test.Combinators
import Test.Parser

/-! Parser regression checks. `#guard` runs at elaboration, so a false guard is a build
error and turns the `core` CI job red. -/

/-! ### Sanity: the graded byte backend parses. -/
section
open Grip

private
def digits
    : GParser conditional Nat
    :=
  GParser.takeWhile1 (fun b => 48 ≤ b && b ≤ 57)

private
def sample
    :=
  GParser.seqR (GParser.byte 40) (GParser.seqL digits (GParser.byte 41))  -- "(" digits ")"

#guard (GParser.run? digits "123".toUTF8) == some 3        -- 3 digit bytes consumed
#guard (GParser.run? sample "(42)".toUTF8) == some 2       -- 2 digit bytes inside parens
#guard (GParser.run? sample "(42".toUTF8) == none          -- missing ')'
#guard (GParser.run? (GParser.foldMany (· + ·) 0 digits) "".toUTF8) == some 0

/-! ### Incremental migration: recover one precise primitive without grading the caller. -/

private
def migratedDigits
    : GParser conditional Nat
    :=
  GParser.takeWhile1 Ascii.isDigit

private
def migratedGroups
    : Parser (List Nat)
    :=
  GParser.many migratedDigits

#guard (GParser.run? migratedGroups "12".toUTF8) == some [2]

-- fix: a recursive nested-parens parser returning the nesting depth. Each level
-- consumes "(" before recursing; unbalanced input fails.
private
def parenDepth
    : GParser conditional Nat
    :=
  GParser.fix fun self =>
    GParser.map (· + 1)
      (GParser.seqR (GParser.byte 40)
        (GParser.seqL (GParser.alt self (GParser.pure 0)) (GParser.byte 41)))

#guard (GParser.run? parenDepth "()".toUTF8) == some 1
#guard (GParser.run? parenDepth "((()))".toUTF8) == some 3
#guard (GParser.run? parenDepth "(()".toUTF8) == none            -- unbalanced

-- Direct left recursion type-checks, but the input-bounded fuel makes it terminate as a
-- failure instead of looping. Guarded bodies such as `parenDepth` above have the stronger
-- completeness theorem; the `conditional → conditional` transformer type alone is insufficient.
private
def directLeft
    : GParser conditional Unit
    :=
  GParser.fix fun self => self

#guard (match directLeft.run "x".toUTF8 0 with
| .error e => e.pos == 0 && e.pos ≤ "x".toUTF8.size
| .ok _ _ => false)

-- BEq for ParseResult, needed by the #guard comparisons below.
private
instance instBEqParseResult
    {β : Type}
    [BEq β]
    : BEq (ParseResult β)
    where
  beq
    | .error e1, .error e2 => e1 == e2
    | .ok a p,   .ok b q   => a == b && p == q
    | _,         _         => false

-- Error payload: bare failure records pos; label sets expected.
#guard (digits.run "abc".toUTF8 0 == (.error { pos := 0 } : ParseResult Nat))
#guard ((digits <?> "digit").run "abc".toUTF8 0
        == (.error { pos := 0, expected := ["digit"] } : ParseResult Nat))
-- Tie-merge: both branches fail at pos 0; expected sets are unioned.
private def byteA : GParser conditional Unit := GParser.byte 65
private def byteB : GParser conditional Unit := GParser.byte 66
#guard ((GParser.alt (byteA <?> "A") (byteB <?> "B")).run "c".toUTF8 0
        == (.error { pos := 0, expected := ["A", "B"] } : ParseResult Unit))

-- gdo names what it supports instead of failing on an elaborator internal.
/--
error: gdo supports `let x ← p`, `let x := e`, bare parser lines, `return`, and a final
`grade_by`; write anything else with `GParser.bind`
-/
#guard_msgs (whitespace := lax) in
example
    : GParser conditional Unit
    :=
  gdo
    if true then byteA else byteB
    byteA

end
