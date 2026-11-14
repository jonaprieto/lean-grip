/-
Copyright (c) 2026 Jonathan Cubides. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Prieto-Cubides

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
@[inline]
def oneOf
    (bs : List UInt8)
    : GParser conditional UInt8
    :=
  satisfy (fun b => bs.contains b)
/-- One byte not in `bs`. -/
@[inline]
def noneOf
    (bs : List UInt8)
    : GParser conditional UInt8
    :=
  satisfy (fun b => !bs.contains b)

/-! ### Higher-order combinators -/

/-- `p` between `open`/`close`; grades multiply (megaparsec order: open, close, body). -/
@[inline]
def between
    (open_ : GParser g₁ β)
    (close : GParser g₂ γ)
    (p : GParser g α)
    : GParser (g₁ * (g * g₂)) α
    :=
  seqR open_ (seqL p close)

/-- One or more `p` separated by `sep`; both must always consume. -/
@[inline]
def sepBy1
    (p : GParser conditional α)
    (sep : GParser conditional β)
    : GParser conditional (List α)
    :=
  map2 (fun x xs => x :: xs) p (many (seqR sep p))

/-- Zero or more `p` separated by `sep`. -/
@[inline]
def sepBy
    (p : GParser conditional α)
    (sep : GParser conditional β)
    : GParser flexible (List α)
    :=
  alt (sepBy1 p sep) (pure [])

/-- Zero or more `p` each followed by `sep`. -/
@[inline]
def endBy
    (p : GParser conditional α)
    (sep : GParser conditional β)
    : GParser flexible (List α)
    :=
  many (seqL p sep)

/-- One or more `p` each followed by `sep`. -/
@[inline]
def endBy1
    (p : GParser conditional α)
    (sep : GParser conditional β)
    : GParser conditional (List α)
    :=
  map2 (fun x xs => x :: xs) (seqL p sep) (endBy p sep)

/-- One or more `p` (always-consuming); the grade is the element parser's. -/
@[inline]
def many1
    (p : GParser ⟨ge, always⟩ α)
    : GParser ⟨ge, always⟩ (List α)
    :=
  gcast (by cases ge <;> rfl) (map2 (fun x xs => x :: xs) p (many p))

/-- Skip zero or more `p` (always-consuming); returns the count skipped. -/
@[inline]
def skipMany
    (p : GParser ⟨ge, always⟩ α)
    : GParser flexible Nat
    :=
  foldMany (fun n _ => n + 1) 0 p

/-- Skip one or more `p` (always-consuming); returns the count. -/
@[inline]
def skipMany1
    (p : GParser conditional α)
    : GParser conditional Nat
    :=
  map2 (fun _ n => n + 1) p (skipMany p)

/-- `p`, or `x` if `p` fails. Never fails; consumption follows `p`'s grade. -/
@[inline]
def option
    (x : α)
    (p : GParser g α)
    : GParser (Grade.choice g 1) α
    :=
  alt p (pure x)

/-- `some` of `p`, or `none`. Never fails; consumption follows `p`'s grade. -/
@[inline]
def optional
    (p : GParser g α)
    : GParser (Grade.choice g 1) (Option α)
    :=
  alt (map some p) (pure none)

/-- Succeed (consuming nothing) exactly when `p` fails. -/
@[inline]
def notFollowedBy
    (p : GParser g α)
    : GParser lookahead Unit
    where
  run := fun arr q => match p.run arr q with | .ok _ _ => .error { pos := q } | .error _ => .ok () q
  cwit := by
    intro arr q a q' h
    split at h
    · nomatch h
    · simp only [ParseResult.ok.injEq] at h
      exact h.2
  ewit := nofun
  swit := nofun
  bwit := by
    intro arr q a q' hq h
    split at h
    · nomatch h
    · simp only [ParseResult.ok.injEq] at h
      omega
  fwit := by
    intro arr q e hq h
    split at h
    · simp only [ParseResult.error.injEq] at h
      subst e
      exact ⟨Nat.le_refl q, hq⟩
    · contradiction
/-- Zero or more `p` until `endp` succeeds; `endp`'s result is discarded and the `p`
results are collected. Total via `fix`; both parsers must always consume. -/
@[inline]
def manyTill
    (p : GParser conditional α)
    (endp : GParser conditional β)
    : GParser conditional (List α)
    :=
  fix fun rec =>
    alt (map (fun _ => ([] : List α)) endp)
      (map2 (fun x xs => x :: xs) p rec)

/-- End of input: succeed (consuming nothing) exactly when no byte remains. Defined as
`notFollowedBy` of the any-byte parser; used to reject trailing input after a top-level parse.
Labelled, since a failure here always means the same thing: something followed what should
have been the last byte. -/
@[inline]
def eof
    : GParser lookahead Unit
    :=
  notFollowedBy (satisfy (fun _ => true)) <?> "end of input"

/-- Try `ps` in order at `q` after an earlier failure `err`: the first success wins, and each
failure merges into `err` (`Err.merge`). This is what a left fold of `alt` over `ps` runs, without
building the nested closures. -/
def chooseFwd
    (arr : ByteArray)
    (q : Nat)
    : Err →
      List (GParser g α) →
      ParseResult α
  | err, [] => .error err
  | err, p :: ps =>
    match p.run arr q with
    | .ok a q' => .ok a q'
    | .error e => chooseFwd arr q (err.merge e) ps

/-- A `chooseFwd` success is a success of one of the alternatives. -/
theorem chooseFwd_ok
    {arr : ByteArray}
    {q : Nat}
    {err : Err}
    {ps : List (GParser g α)}
    {a : α}
    {q' : Nat}
    (h : chooseFwd arr q err ps = .ok a q')
    : ∃ p ∈ ps, p.run arr q = .ok a q'
    := by
  induction ps generalizing err with
  | nil => nomatch h
  | cons p ps ih =>
    simp only [chooseFwd] at h
    split at h
    · rename_i hp
      simp only [ParseResult.ok.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨p, List.mem_cons_self, hp⟩
    · obtain ⟨p', hm, hp'⟩ := ih h
      exact ⟨p', List.mem_cons_of_mem _ hm, hp'⟩

/-- A `chooseFwd` failure from an in-bounds start stays between the start and EOF when `err`
does. -/
theorem chooseFwd_error
    {arr : ByteArray}
    {q : Nat}
    {err : Err}
    {ps : List (GParser g α)}
    {e : Err}
    (hq : q ≤ arr.size)
    (herr : q ≤ err.pos ∧ err.pos ≤ arr.size)
    (h : chooseFwd arr q err ps = .error e)
    : q ≤ e.pos ∧
      e.pos ≤ arr.size
    := by
  induction ps generalizing err with
  | nil =>
    simp only [chooseFwd, ParseResult.error.injEq] at h
    subst e
    exact herr
  | cons p ps ih =>
    simp only [chooseFwd] at h
    split at h
    · nomatch h
    · rename_i e' hp
      refine ih ?_ h
      rcases Err.merge_pos err e' with hm | hm <;> rw [hm]
      · exact herr
      · exact p.fwit hq hp

/-- An all-failing `chooseFwd` fails. -/
theorem chooseFwd_fails
    {arr : ByteArray}
    {q : Nat}
    {ps : List (GParser g α)}
    (hps : ∀ p ∈ ps, ∃ e, p.run arr q = .error e)
    (err : Err)
    : ∃ e, chooseFwd arr q err ps = .error e
    := by
  induction ps generalizing err with
  | nil => exact ⟨err, rfl⟩
  | cons p ps ih =>
    obtain ⟨e', hp⟩ := hps p List.mem_cons_self
    simp only [chooseFwd, hp]
    exact ih (fun p' hm => hps p' (List.mem_cons_of_mem _ hm)) _

/-- Ordered choice over a non-empty list at a single grade `g`: `x`, then each of `xs`, with
failures merged as `alt` merges them. -/
@[inline]
def chooseG
    (x : GParser g α)
    (xs : List (GParser g α))
    : GParser g α
    where
  run arr q :=
    match x.run arr q with
    | .ok a q' => .ok a q'
    | .error e => chooseFwd arr q e xs
  cwit := by
    intro arr q a q' h
    split at h
    · rename_i hx
      simp only [ParseResult.ok.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact x.cwit hx
    · obtain ⟨p, _, hp⟩ := chooseFwd_ok h
      exact p.cwit hp
  ewit := by
    intro he arr q
    obtain ⟨ex, hx⟩ := x.ewit he arr q
    simp only [hx]
    exact chooseFwd_fails (fun p _ => p.ewit he arr q) ex
  swit := by
    intro he arr q
    obtain ⟨a, q', hx⟩ := x.swit he arr q
    exact ⟨a, q', by simp only [hx]⟩
  bwit := by
    intro arr q a q' hq h
    split at h
    · rename_i hx
      simp only [ParseResult.ok.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact x.bwit hq hx
    · obtain ⟨p, _, hp⟩ := chooseFwd_ok h
      exact p.bwit hq hp
  fwit := by
    intro arr q e hq h
    split at h
    · nomatch h
    · rename_i ex hx
      exact chooseFwd_error hq (x.fwit hq hx) h

/-- What `choice` runs: `ps` in order at `q`, the first success winning and failures merging
right to left, as a right fold of `alt` ending in a failure at `q` does. Recursion is on the list,
which is short. -/
def choiceFwd
    (arr : ByteArray)
    (q : Nat)
    : List (Parser α) →
      ParseResult α
  | [] => .error { pos := q }
  | p :: ps =>
    match p.run arr q with
    | .ok a q' => .ok a q'
    | .error ex =>
      match choiceFwd arr q ps with
      | .ok a q' => .ok a q'
      | .error ey => .error (ex.merge ey)

/-- A `choiceFwd` success is a success of one of the alternatives. -/
theorem choiceFwd_ok
    {arr : ByteArray}
    {q : Nat}
    {ps : List (Parser α)}
    {a : α}
    {q' : Nat}
    (h : choiceFwd arr q ps = .ok a q')
    : ∃ p ∈ ps, p.run arr q = .ok a q'
    := by
  induction ps with
  | nil => nomatch h
  | cons p ps ih =>
    simp only [choiceFwd] at h
    split at h
    · rename_i hp
      simp only [ParseResult.ok.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨p, List.mem_cons_self, hp⟩
    · split at h
      · rename_i hr
        obtain ⟨p', hm, hp'⟩ := ih (by rw [hr]; exact h)
        exact ⟨p', List.mem_cons_of_mem _ hm, hp'⟩
      · nomatch h

/-- A `choiceFwd` failure from an in-bounds start reports a position between the start and EOF. -/
theorem choiceFwd_error
    {arr : ByteArray}
    {q : Nat}
    {ps : List (Parser α)}
    {e : Err}
    (hq : q ≤ arr.size)
    (h : choiceFwd arr q ps = .error e)
    : q ≤ e.pos ∧
      e.pos ≤ arr.size
    := by
  induction ps generalizing e with
  | nil =>
    simp only [choiceFwd, ParseResult.error.injEq] at h
    subst e
    exact ⟨Nat.le_refl q, hq⟩
  | cons p ps ih =>
    simp only [choiceFwd] at h
    split at h
    · nomatch h
    · rename_i ex hp
      split at h
      · nomatch h
      · rename_i ey hr
        simp only [ParseResult.error.injEq] at h
        subst e
        rcases Err.merge_pos ex ey with hm | hm <;> rw [hm]
        · exact p.fwit hq hp
        · exact ih hr

/-- Ordered choice at the ungraded `Parser` face; empty list fails. -/
@[inline]
def choice
    (ps : List (Parser α))
    : Parser α
    where
  run arr q := choiceFwd arr q ps
  cwit := by
    intro arr q a q' h
    obtain ⟨p, _, hp⟩ := choiceFwd_ok h
    exact p.cwit hp
  ewit := nofun
  swit := nofun
  bwit := by
    intro arr q a q' hq h
    obtain ⟨p, _, hp⟩ := choiceFwd_ok h
    exact p.bwit hq hp
  fwit := fun hq h => choiceFwd_error hq h

/-- Exactly `n` copies of `p`, at the `Parser` face (grade is `n`-dependent). -/
def count
    (n : Nat)
    (p : Parser α)
    : Parser (List α)
    := do
  match n with
  | 0 => return []
  | n + 1 => let x ← p; let xs ← count n p; return (x :: xs)

end GParser

/-! ### Notation

The familiar parser-combinator operators, at the graded level (grades multiply/combine as
the underlying combinator dictates). `scoped`, so they activate on `open Grip`. The
`Parser` (ungraded) face additionally gets the standard `Monad`/`Alternative` operators.
A `Parser` is a `GParser fallible`, so with `open Grip` an operator on two `Parser` operands
matches both readings and Lean reports an ambiguous term; at that face use the named
combinators or leave `Grip` closed. The label operator `<?>` is global (declared with the
core). -/

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
