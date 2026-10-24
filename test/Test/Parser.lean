/-
Copyright (c) 2026 Jonathan Cubides. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Prieto-Cubides
-/
import Grip

/-! Checks for `Grip.Parser`, run at elaboration by `lake build Test`. -/

section Guards
open Grip

-- Coercion: a `conditional` parser coerces to `Parser` via the `CoeOut` instance.
-- The coercion is "source-driven" (left-to-right), so no explicit cast annotation needed.
private
def digitP
    : Parser UInt8
    :=
  GParser.satisfy (fun b => 48 ≤ b && b ≤ 57)

example (f : UInt8 → Bool) : Parser UInt8 := GParser.satisfy f

-- `Monad` do-notation collapses grade to `fallible`; `#guard` checks round-trip.
private
def twoDigits
    : Parser (UInt8 × UInt8)
    := do
  let a ← digitP
  let b ← digitP
  return (a, b)

#guard (GParser.run? twoDigits "57".toUTF8) == some (53, 55)

-- `Alternative`: `<|>` and `failure` work at `Parser`.
private
def digitOrFail
    : Parser UInt8
    :=
  digitP <|> failure

#guard (GParser.run? digitOrFail "5".toUTF8) == some 53
#guard (GParser.run? digitOrFail "/".toUTF8) == none

-- `GParser.many` requires `consumes = always`; `conditional` qualifies.
-- Uncommenting the line below would produce a TYPE ERROR (pure has `consumes = never`):
--   #check GParser.many (GParser.pure (0 : Nat))
example : GParser flexible (List UInt8) := GParser.many (GParser.satisfy (· != 0))

-- `gdo`: grade is preserved precisely (stays `conditional`, not collapsed to `fallible`).
-- `conditional * conditional = conditional` because
--   `max always always = always` and `max possibly possibly = possibly` both hold.
private
def twoBytes
    : GParser conditional (UInt8 × UInt8)
    :=
  gdo
    let a ← GParser.satisfy (fun _ => true)
    let b ← GParser.satisfy (fun _ => true)
    return (a, b)

#guard (GParser.run? twoBytes "AB".toUTF8) == some (65, 66)
#guard (GParser.run? twoBytes "".toUTF8) == none

-- BEq for Except ParseError, needed by the #guard comparisons below.
private
instance instBEqExceptPE
    {β : Type}
    [BEq β]
    : BEq (Except ParseError β)
    where
  beq
    | .error e1, .error e2 => e1 == e2
    | .ok a,     .ok b     => a == b
    | _,         _         => false

-- `GParser.parse` surfaces a `ParseError` with positioned information.
private
def digitOrErr
    : Parser Nat
    :=
  GParser.weakenFallible (GParser.nat <?> "number")

#guard (digitOrErr.parse "abc".toUTF8
        == (.error { pos := 0, line := 1, col := 1, expected := ["number"] } :
            Except ParseError Nat))
#guard (digitOrErr.parse "42".toUTF8 == (.ok 42 : Except ParseError Nat))

-- `pretty` is the dependency-free plain fallback; rich terminal output lives in
-- `grip-diagnostics` and delegates to `TermColor.Diagnostics`.
private
def prettyTest
    : String
    :=
  let e : ParseError := { pos := 5, line := 3, col := 2, expected := ["!"] }
  e.pretty "a\nb\n1".toUTF8

#guard prettyTest == "3:2: expected !\n1\n ^"

end Guards
