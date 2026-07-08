/-
Copyright 2026 Jonathan Cubides. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grip.Parser
import Grip.Ascii

/-!
# Grip.Combinators -- a megaparsec-style vocabulary over the grip core

Ready-made byte parsers (`ws`, `digit`, `oneOf`, ...) and higher-order combinators
(`sepBy`, `between`, `choice`, ...), each with a precise grade where the grade is stable,
or at the `Parser` (fallible) face where it depends on runtime data. Batteries-only.
-/

open Necessity
open Grip.Ascii

namespace Grip

variable {α β γ : Type} {g g₁ g₂ : Grade} {ge : Necessity}

/-! ### Byte parsers -/

/-- Match the byte of an ASCII `Char` literal: `byteC '{'` matches `{`. -/
@[inline] def GParser.byteC (c : Char) : GParser conditional Unit := GParser.byte (Ascii.code c)
/-- Skip zero or more whitespace bytes; returns the count. -/
@[inline] def GParser.ws : GParser flexible Nat := GParser.takeWhile Ascii.isWs
/-- Skip one or more whitespace bytes; returns the count. -/
@[inline] def GParser.ws1 : GParser conditional Nat := GParser.takeWhile1 Ascii.isWs
/-- One decimal digit byte. -/
@[inline] def GParser.digit : GParser conditional UInt8 := GParser.satisfy Ascii.isDigit
/-- One hex digit byte. -/
@[inline] def GParser.hexDigit : GParser conditional UInt8 := GParser.satisfy Ascii.isHexDigit
/-- One ASCII letter byte. -/
@[inline] def GParser.letter : GParser conditional UInt8 := GParser.satisfy Ascii.isAlpha
/-- One letter-or-digit byte. -/
@[inline] def GParser.alphaNum : GParser conditional UInt8 := GParser.satisfy Ascii.isAlphaNum
/-- One uppercase letter byte. -/
@[inline] def GParser.upper : GParser conditional UInt8 := GParser.satisfy Ascii.isUpper
/-- One lowercase letter byte. -/
@[inline] def GParser.lower : GParser conditional UInt8 := GParser.satisfy Ascii.isLower
/-- One byte from `bs`. -/
@[inline] def GParser.oneOf (bs : List UInt8) : GParser conditional UInt8 :=
  GParser.satisfy (fun b => bs.contains b)
/-- One byte not in `bs`. -/
@[inline] def GParser.noneOf (bs : List UInt8) : GParser conditional UInt8 :=
  GParser.satisfy (fun b => !bs.contains b)

/-! ### Higher-order combinators -/

/-- `p` between `open`/`close`; grades multiply (megaparsec order: open, close, body). -/
@[inline] def GParser.between (open_ : GParser g₁ β) (close : GParser g₂ γ) (p : GParser g α) :
    GParser (g₁ * (g * g₂)) α :=
  GParser.seqR open_ (GParser.seqL p close)

/-- One or more `p` separated by `sep`; both must always consume. -/
@[inline] def GParser.sepBy1 (p : GParser conditional α) (sep : GParser conditional β) :
    GParser conditional (List α) :=
  GParser.map2 (fun x xs => x :: xs) p (GParser.many (GParser.seqR sep p))

/-- Zero or more `p` separated by `sep`. -/
@[inline] def GParser.sepBy (p : GParser conditional α) (sep : GParser conditional β) :
    GParser flexible (List α) :=
  GParser.alt (GParser.sepBy1 p sep) (GParser.pure [])

/-- Zero or more `p` each followed by `sep`. -/
@[inline] def GParser.endBy (p : GParser conditional α) (sep : GParser conditional β) :
    GParser flexible (List α) :=
  GParser.many (GParser.seqL p sep)

/-- Skip zero or more `p` (always-consuming); returns the count skipped. -/
@[inline] def GParser.skipMany (p : GParser ⟨ge, always⟩ α) : GParser flexible Nat :=
  GParser.foldMany (fun n _ => n + 1) 0 p

/-- Skip one or more `p` (always-consuming); returns the count. -/
@[inline] def GParser.skipMany1 (p : GParser conditional α) : GParser conditional Nat :=
  GParser.map2 (fun _ n => n + 1) p (GParser.skipMany p)

/-- `p`, or `x` if `p` fails. -/
@[inline] def GParser.option (x : α) (p : GParser g α) := GParser.alt p (GParser.pure x)

/-- `some` of `p`, or `none`. -/
@[inline] def GParser.optional (p : GParser g α) :=
  GParser.alt (GParser.map some p) (GParser.pure none)

/-- Succeed (consuming nothing) exactly when `p` fails. -/
@[inline] def GParser.notFollowedBy (p : GParser g α) : GParser ⟨possibly, never⟩ Unit where
  run := fun arr q => match p.run arr q with | .ok _ _ => .error ⟨q, []⟩ | .error _ => .ok () q
  cwit := by
    intro arr q a q' h
    split at h
    · exact absurd h (by simp)
    · simp only [ParseResult.ok.injEq] at h
      exact h.2
  ewit := by intro he; exact absurd he (by decide)
  swit := by intro he; exact absurd he (by decide)

/-- Zero or more `p` until `endp` matches; `endp` is discarded. -/
@[inline] def GParser.manyTill (p : GParser conditional α) (endp : GParser conditional β) :
    GParser conditional (List α) :=
  GParser.fix fun rec =>
    GParser.alt (GParser.map (fun _ => ([] : List α)) endp)
      (GParser.map2 (fun x xs => x :: xs) p rec)

/-- Ordered choice is idempotent on the grade: choosing between two parsers of the same
grade stays at that grade. -/
private theorem choice_self (g : Grade) : Grade.choice g g = g := by
  cases g with | mk e c => cases e <;> cases c <;> rfl

/-- Ordered choice over a non-empty list at a single grade `g`. The grade is preserved
via `choice_self` (choosing between two grade-`g` parsers is again grade `g`). -/
@[inline] def GParser.chooseG (x : GParser g α) (xs : List (GParser g α)) : GParser g α :=
  xs.foldl (fun acc p => GParser.gcast (choice_self g) (GParser.alt acc p)) x

/-- Ordered choice at the ungraded `Parser` face; empty list fails. -/
@[inline] def choice (ps : List (Parser α)) : Parser α :=
  ps.foldr (fun p acc => GParser.weakenFallible (GParser.alt p acc))
    (GParser.weakenFallible GParser.fail)

/-- Exactly `n` copies of `p`, at the `Parser` face (grade is `n`-dependent). -/
def count (n : Nat) (p : Parser α) : Parser (List α) := do
  match n with
  | 0 => return []
  | n + 1 => let x ← p; let xs ← count n p; return (x :: xs)

/-! ### Notation

The familiar parser-combinator operators, at the graded level (grades multiply/combine as
the underlying combinator dictates). `scoped`, so they activate on `open Grip`. The
`Parser` (ungraded) face additionally gets the standard `Monad`/`Alternative` operators
for free; these graded versions coexist with those and are chosen when the operands are
graded `GParser`s. The label operator `<?>` is global (declared with the core). -/

/-- Functor map: `f <$> p`. -/
scoped infixr:100 " <$> " => GParser.map
/-- Replace the result with a constant: `x <$ p`. -/
scoped infixr:100 " <$ "  => fun x p => GParser.map (fun _ => x) p
/-- Applicative apply: `pf <*> px`; grades multiply. -/
scoped infixl:60  " <*> " => fun pf px => GParser.map2 (fun f x => f x) pf px
/-- Sequence, keep the right result: `p *> q`; grades multiply. -/
scoped infixl:60  " *> "  => GParser.seqR
/-- Sequence, keep the left result: `p <* q`; grades multiply. -/
scoped infixl:60  " <* "  => GParser.seqL
/-- Ordered choice: `p <|> q`; grade follows `Grade.choice`. -/
scoped infixl:20  " <|> " => GParser.alt

end Grip

/-! ### Sanity guards. -/
section
open Grip

#guard (GParser.run? GParser.digit "7".toUTF8) == some 55
#guard (GParser.run? GParser.digit "x".toUTF8) == none
#guard (GParser.run? GParser.hexDigit "f".toUTF8) == some 102
#guard (GParser.run? (GParser.byteC '{') "{".toUTF8) == some ()
#guard (GParser.run? GParser.ws "  \tx".toUTF8) == some 3
#guard (GParser.run? GParser.ws1 "x".toUTF8) == none
#guard (GParser.run? (GParser.oneOf [97, 98]) "b".toUTF8) == some 98
#guard (GParser.run? (GParser.noneOf [97, 98]) "b".toUTF8) == none

#guard (GParser.run? (GParser.sepBy GParser.digit (GParser.byteC ',')) "1,2,3".toUTF8)
        == some [49, 50, 51]
#guard (GParser.run? (GParser.sepBy GParser.digit (GParser.byteC ',')) "".toUTF8) == some []
#guard (GParser.run? (GParser.between (GParser.byteC '(') (GParser.byteC ')') GParser.digit) "(5)".toUTF8)
        == some 53
#guard (GParser.run? (GParser.endBy GParser.digit (GParser.byteC ';')) "1;2;".toUTF8) == some [49, 50]
#guard (GParser.run? (GParser.skipMany GParser.digit) "123x".toUTF8) == some 3
#guard (GParser.run? (GParser.option (65 : UInt8) GParser.digit) "x".toUTF8) == some 65
#guard (GParser.run? (GParser.optional GParser.digit) "x".toUTF8) == some none
#guard (GParser.run? (GParser.notFollowedBy GParser.digit) "x".toUTF8) == some ()
#guard (GParser.run? (GParser.notFollowedBy GParser.digit) "5".toUTF8) == none
#guard (GParser.run? (GParser.manyTill GParser.letter (GParser.byteC '.')) "abc.".toUTF8)
        == some [97, 98, 99]
#guard (GParser.run? (GParser.chooseG (GParser.byteC 'a') [GParser.byteC 'b']) "b".toUTF8) == some ()
#guard (GParser.run? (choice [GParser.weakenFallible (GParser.byteC 'a'),
                              GParser.weakenFallible (GParser.byteC 'b')]) "b".toUTF8) == some ()
#guard (GParser.run? (count 3 (GParser.weakenFallible GParser.digit)) "123".toUTF8)
        == some [49, 50, 51]

-- notation (graded): <$> <$ <*> *> <* <|>
#guard (GParser.run? ((fun _ => (7 : Nat)) <$> GParser.digit) "5".toUTF8) == some 7
#guard (GParser.run? ((9 : Nat) <$ GParser.digit) "5".toUTF8) == some 9
#guard (GParser.run? (GParser.byteC '(' *> GParser.digit <* GParser.byteC ')') "(5)".toUTF8) == some 53
#guard (GParser.run? (GParser.digit <|> GParser.letter) "a".toUTF8) == some 97
#guard (GParser.run? ((fun (a : UInt8) (b : UInt8) => (a, b)) <$> GParser.digit <*> GParser.digit) "78".toUTF8)
        == some (55, 56)

end
