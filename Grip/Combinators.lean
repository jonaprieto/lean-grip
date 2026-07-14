/-
Copyright (c) 2026 Jonathan Cubides. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Cubides

Inspired by prim-parser by Jan Mas Rovira
(https://github.com/janmasrovira/prim-parser): the grade-tracking combinator
style and the guardedness gate on `many`. The combinators themselves follow
the standard megaparsec/parsec vocabulary.
-/
import Grip.Parser
import Grip.Ascii

/-!
# Grip.Combinators: a megaparsec-style vocabulary over the grip core

Ready-made byte parsers (`ws`, `digit`, `oneOf`, ...) and higher-order combinators
(`sepBy`, `between`, `choice`, ...), each with a precise grade where the grade is stable,
or at the `Parser` (fallible) face where it depends on runtime data. Batteries-only.
-/

open Modality
open Grip.Ascii

namespace Grip

variable {α β γ : Type} {g g₁ g₂ : Grade} {ge : Modality}

namespace GParser

/-! ### Byte parsers -/

/-- Match the byte of an ASCII `Char` literal: `ch '{'` matches `{`. -/
@[inline] def ch (c : Char) : GParser conditional Unit := byte (Ascii.code c)
/-- Skip zero or more whitespace bytes; returns the count. -/
@[inline] def ws : GParser flexible Nat := takeWhile Ascii.isWs
/-- Skip one or more whitespace bytes; returns the count. -/
@[inline] def ws1 : GParser conditional Nat := takeWhile1 Ascii.isWs
/-- One decimal digit byte. -/
@[inline] def digit : GParser conditional UInt8 := satisfy Ascii.isDigit
/-- One hex digit byte. -/
@[inline] def hexDigit : GParser conditional UInt8 := satisfy Ascii.isHexDigit
/-- One ASCII letter byte. -/
@[inline] def letter : GParser conditional UInt8 := satisfy Ascii.isAlpha
/-- One letter-or-digit byte. -/
@[inline] def alphaNum : GParser conditional UInt8 := satisfy Ascii.isAlphaNum
/-- One uppercase letter byte. -/
@[inline] def upper : GParser conditional UInt8 := satisfy Ascii.isUpper
/-- One lowercase letter byte. -/
@[inline] def lower : GParser conditional UInt8 := satisfy Ascii.isLower
/-- One byte from `bs`. -/
@[inline] def oneOf (bs : List UInt8) : GParser conditional UInt8 :=
  satisfy (fun b => bs.contains b)
/-- One byte not in `bs`. -/
@[inline] def noneOf (bs : List UInt8) : GParser conditional UInt8 :=
  satisfy (fun b => !bs.contains b)

/-! ### Higher-order combinators -/

/-- `p` between `open`/`close`; grades multiply (megaparsec order: open, close, body). -/
@[inline] def between (open_ : GParser g₁ β) (close : GParser g₂ γ) (p : GParser g α) :
    GParser (g₁ * (g * g₂)) α :=
  seqR open_ (seqL p close)

/-- One or more `p` separated by `sep`; both must always consume. -/
@[inline] def sepBy1 (p : GParser conditional α) (sep : GParser conditional β) :
    GParser conditional (List α) :=
  map2 (fun x xs => x :: xs) p (many (seqR sep p))

/-- Zero or more `p` separated by `sep`. -/
@[inline] def sepBy (p : GParser conditional α) (sep : GParser conditional β) :
    GParser flexible (List α) :=
  alt (sepBy1 p sep) (pure [])

/-- Zero or more `p` each followed by `sep`. -/
@[inline] def endBy (p : GParser conditional α) (sep : GParser conditional β) :
    GParser flexible (List α) :=
  many (seqL p sep)

/-- Skip zero or more `p` (always-consuming); returns the count skipped. -/
@[inline] def skipMany (p : GParser ⟨ge, always⟩ α) : GParser flexible Nat :=
  foldMany (fun n _ => n + 1) 0 p

/-- Skip one or more `p` (always-consuming); returns the count. -/
@[inline] def skipMany1 (p : GParser conditional α) : GParser conditional Nat :=
  map2 (fun _ n => n + 1) p (skipMany p)

/-- `p`, or `x` if `p` fails. -/
@[inline] def option (x : α) (p : GParser g α) := alt p (pure x)

/-- `some` of `p`, or `none`. -/
@[inline] def optional (p : GParser g α) :=
  alt (map some p) (pure none)

/-- Succeed (consuming nothing) exactly when `p` fails. -/
@[inline] def notFollowedBy (p : GParser g α) : GParser ⟨possibly, never⟩ Unit where
  run := fun arr q => match p.run arr q with | .ok _ _ => .error ⟨q, []⟩ | .error _ => .ok () q
  cwit := by
    intro arr q a q' h
    split at h
    · exact absurd h (by simp)
    · simp only [ParseResult.ok.injEq] at h
      exact h.2
  ewit := by intro he; exact absurd he (by decide)
  swit := by intro he; exact absurd he (by decide)
  bwit := by
    intro arr q a q' hq h
    split at h
    · exact absurd h (by simp)
    · simp only [ParseResult.ok.injEq] at h
      omega
@[inline] def manyTill (p : GParser conditional α) (endp : GParser conditional β) :
    GParser conditional (List α) :=
  fix fun rec =>
    alt (map (fun _ => ([] : List α)) endp)
      (map2 (fun x xs => x :: xs) p rec)

/-- End of input: succeed (consuming nothing) exactly when no byte remains. The dual of
`notFollowedBy` applied to "any byte", used to reject trailing input after a top-level parse. -/
@[inline] def eof : GParser ⟨possibly, never⟩ Unit :=
  notFollowedBy (satisfy (fun _ => true))

/-- Ordered choice is idempotent on the grade: choosing between two parsers of the same
grade stays at that grade. -/
private theorem choice_self (g : Grade) : Grade.choice g g = g := by
  cases g with | mk e c => cases e <;> cases c <;> rfl

/-- Ordered choice over a non-empty list at a single grade `g`. The grade is preserved
via `choice_self` (choosing between two grade-`g` parsers is again grade `g`). -/
@[inline] def chooseG (x : GParser g α) (xs : List (GParser g α)) : GParser g α :=
  xs.foldl (fun acc p => gcast (choice_self g) (alt acc p)) x

/-- Ordered choice at the ungraded `Parser` face; empty list fails. -/
@[inline] def choice (ps : List (Parser α)) : Parser α :=
  ps.foldr (fun p acc => weakenFallible (alt p acc))
    (weakenFallible fail)

/-- Exactly `n` copies of `p`, at the `Parser` face (grade is `n`-dependent). -/
def count (n : Nat) (p : Parser α) : Parser (List α) := do
  match n with
  | 0 => return []
  | n + 1 => let x ← p; let xs ← count n p; return (x :: xs)

end GParser

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
open Grip GParser

#guard (run? digit "7".toUTF8) == some 55
#guard (run? digit "x".toUTF8) == none
#guard (run? hexDigit "f".toUTF8) == some 102
#guard (run? (ch '{') "{".toUTF8) == some ()
#guard (run? ws "  \tx".toUTF8) == some 3
#guard (run? ws1 "x".toUTF8) == none
#guard (run? (oneOf [97, 98]) "b".toUTF8) == some 98
#guard (run? (noneOf [97, 98]) "b".toUTF8) == none

#guard (run? (sepBy digit (ch ',')) "1,2,3".toUTF8)
        == some [49, 50, 51]
#guard (run? (sepBy digit (ch ',')) "".toUTF8) == some []
#guard (run? (between (ch '(') (ch ')') digit) "(5)".toUTF8)
        == some 53
#guard (run? (endBy digit (ch ';')) "1;2;".toUTF8) == some [49, 50]
#guard (run? (skipMany digit) "123x".toUTF8) == some 3
#guard (run? (option (65 : UInt8) digit) "x".toUTF8) == some 65
#guard (run? (optional digit) "x".toUTF8) == some none
#guard (run? (notFollowedBy digit) "x".toUTF8) == some ()
#guard (run? (notFollowedBy digit) "5".toUTF8) == none
#guard (run? eof "".toUTF8) == some ()
#guard (run? eof "x".toUTF8) == none
#guard (run? (manyTill letter (ch '.')) "abc.".toUTF8)
        == some [97, 98, 99]
#guard (run? (chooseG (ch 'a') [ch 'b']) "b".toUTF8) == some ()
#guard (run? (choice [weakenFallible (ch 'a'),
                      weakenFallible (ch 'b')]) "b".toUTF8) == some ()
#guard (run? (count 3 (weakenFallible digit)) "123".toUTF8)
        == some [49, 50, 51]

-- notation (graded): <$> <$ <*> *> <* <|>
#guard (run? ((fun _ => (7 : Nat)) <$> digit) "5".toUTF8) == some 7
#guard (run? ((9 : Nat) <$ digit) "5".toUTF8) == some 9
#guard (run? (ch '(' *> digit <* ch ')') "(5)".toUTF8) == some 53
#guard (run? (digit <|> letter) "a".toUTF8) == some 97
#guard (run? ((fun (a : UInt8) (b : UInt8) => (a, b)) <$> digit <*> digit) "78".toUTF8)
        == some (55, 56)

end
