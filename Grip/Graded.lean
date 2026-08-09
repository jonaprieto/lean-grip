/-
Copyright (c) 2026 Jonathan Cubides. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Prieto-Cubides

Adapted from PrimParser/Basic.lean in prim-parser by Jan Mas Rovira
(https://github.com/janmasrovira/prim-parser, commit 5a5ff0d, 2026-05-31):
the grade-indexed parser type and its consumption-witness discipline. grip's
ByteArray/ParseResult core and the fuel-based total fixpoint are its own.
-/

import Grip.Grade
import Grip.Error

/-!
# Grip.Graded: the graded byte-parser type

`GParser g α` is a `run : ByteArray -> Nat -> ParseResult α` (`ok value pos | error e`,
one heap object per successful step, no reified tree) plus five *erased* `Prop`
witnesses tying the static `Grade` (error x consumption `Modality`) to that runtime:

- `cwit`: a success advances the offset exactly as `consumes` claims,
- `ewit`: an `always`-error grade never succeeds (every input yields `.error k`),
- `swit`: a `never`-error grade always succeeds (every input yields `.ok a q'`),
- `bwit`: a success that starts in bounds ends in bounds,
- `fwit`: a failure that starts in bounds reports a position between the start and EOF.

The witnesses erase, so `run` stays the bare `ParseResult` fast path. The failure bound keeps
ordered-choice diagnostics inside the interval being parsed; it does not prove that a
client-provided position is the furthest point actually reached.

This module has the type, the grade-weakening coercion, and the total, fuel-bounded
`fix` combinator. The point combinators live in `Grip.Byte`, the total scanners in
`Grip.Scan`. No mathlib.
-/

open Modality
open Grade

namespace Grip

/-- A byte-level parser with static grade `g`, producing `α`. Successful and failed endpoints
from an in-bounds start are bounded by erased contracts. Built-in choice compares `Err.pos`, but
the type proves only its interval, not that every client parser reports an honest furthest point.

The five `Prop` fields are the *parser soundness* witnesses; they are erased at
runtime (proof-irrelevant, carrying no data), so `run` is the whole runtime cost. -/
structure GParser (g : Grade) (α : Type) where
  /-- Run the parser at an offset, returning `.ok value newOffset` on success or `.error e` on
  failure. -/
  run : ByteArray → Nat → ParseResult α
  /-- Consumption soundness: a successful parse advances the offset exactly as the
  grade's `consumes` component claims (`always ⇒ q<q'`, `possibly ⇒ q≤q'`,
  `never ⇒ q=q'`). -/
  cwit : ∀ {arr q a q'}, run arr q = .ok a q' → consumptionWitness q q' g.consumes
  /-- Error soundness, must-fail direction: a grade claiming `always`-error never
  succeeds: for every input there exists a failure `e`. -/
  ewit : g.errors = always → ∀ arr q, ∃ e : Err, run arr q = .error e
  /-- Error soundness, must-succeed direction: a grade claiming `never`-error always
  succeeds: for every input there exist a value `a` and next offset `q'`. -/
  swit : g.errors = never → ∀ arr q, ∃ a q', run arr q = .ok a q'
  /-- Bounds soundness: a success that starts in bounds ends in bounds
  (`q ≤ arr.size ⇒ q' ≤ arr.size`). Erased, proof-irrelevant. This is the invariant every
  real combinator satisfies; carrying it in the type makes the `impossible` grade
  `⟨never, always⟩` uninhabited outright, with no external hypothesis (see `grip-props`). -/
  bwit : ∀ {arr q a q'}, q ≤ arr.size → run arr q = .ok a q' → q' ≤ arr.size
  /-- Failure-position soundness: a failure from an in-bounds start reports a position no
  earlier than that start and no later than EOF. This bounds choice diagnostics and makes the
  absolute-position/remaining-size correspondence lawful without changing runtime data. -/
  fwit : ∀ {arr q e}, q ≤ arr.size → run arr q = .error e → q ≤ e.pos ∧ e.pos ≤ arr.size

variable {g g' : Grade} {α β : Type}

/-! ### Grade-algebra witness helper lemmas -/

/-- Chain two consumption witnesses across a shared midpoint. Used by the sequencing
combinators in `Grip.Byte`. -/
theorem cw_seq {c0 c1 : Modality} {q r s : Nat}
    (w0 : consumptionWitness q r c0) (w1 : consumptionWitness r s c1) :
    consumptionWitness q s (max c0 c1) := by
  have h := consumptionWitness.trans w1 w0
  rwa [Modality.sup_comm] at h

/-- A success rules out the `always`-error grade (via `ewit`). -/
theorem GParser.errors_ne_always {g : Grade} {α} (p : GParser g α) {arr q a q'}
    (h : p.run arr q = .ok a q') : g.errors ≠ always := fun he => by
  obtain ⟨e, he'⟩ := p.ewit he arr q
  rw [he'] at h; exact absurd h (by simp)

/-- A failure rules out the `never`-error grade (via `swit`). -/
theorem GParser.errors_ne_never {g : Grade} {α} (p : GParser g α) {arr q e}
    (h : p.run arr q = .error e) : g.errors ≠ never := fun he => by
  obtain ⟨a, q', ha⟩ := p.swit he arr q
  rw [ha] at h; exact absurd h (by simp)

/-! ### Running -/

/-- Run a parser from offset 0, returning `some value` on success and `none` on
failure.  The error payload is discarded; use `GParser.parse` (in `Grip.Parser`)
for a positioned `ParseError`. -/
@[inline] def GParser.run? (p : GParser g α) (arr : ByteArray) : Option α :=
  match p.run arr 0 with
  | .ok a _ => some a
  | .error _ => none

/-! ### Grade weakening -/

/-- Weaken a `GParser g α` to a less-precise grade `g'`.

Proofs required:
- `hc`: a success that satisfies `g.consumes` also satisfies `g'.consumes`
- `hew`: `g'.errors = always` implies `g.errors = always` (preserves must-fail)
- `hsw`: `g'.errors = never` implies `g.errors = never` (preserves must-succeed) -/
@[inline] def GParser.weaken {g g' : Grade} (p : GParser g α)
    (hc : ∀ {n m : Nat}, consumptionWitness n m g.consumes → consumptionWitness n m g'.consumes)
    (hew : g'.errors = always → g.errors = always)
    (hsw : g'.errors = never → g.errors = never) : GParser g' α where
  run := p.run
  cwit := fun h => hc (p.cwit h)
  ewit := fun he => p.ewit (hew he)
  swit := fun he => p.swit (hsw he)
  bwit := fun hq h => p.bwit hq h
  fwit := fun hq h => p.fwit hq h

/-- Weaken any parser to `fallible` (errors = possibly, consumes = possibly),
losing all grade precision. Used by the ungraded `Parser` layer. -/
@[inline] def GParser.weakenFallible {g : Grade} (p : GParser g α) : GParser fallible α :=
  p.weaken
    -- Term-mode match so that in each branch `w`'s type is specialised to the
    -- concrete `consumptionWitness` variant before being handed to the proof term.
    (fun {n m} w =>
      match g.consumes, w with
      | always,   (hw : n < m) => Nat.le_of_lt hw
      | possibly, (hw : n ≤ m) => hw
      | never,    (hw : n = m) => hw ▸ Nat.le_refl n)
    (fun h => absurd h (by decide))
    (fun h => absurd h (by decide))



/-! ### Recursion via a fixpoint

`GParser.fix` ties the knot on a parser transformer, giving the body a reference back
to the whole parser so recursive grammars can be written from combinators. The
self-reference is `conditional` (always-consuming), so a well-behaved grammar shrinks
the input before each recursive call.

grip's byte core is not size-indexed: `run` is `ByteArray → Nat → ParseResult`, with no
length in the type, so the kernel cannot see the offset measure `arr.size - q` decrease
through the opaque transformer `f`. Rather than fall back to `partial def`, `fix` recurses on
an explicit fuel (`GParser.fixFuel`), structurally decreasing, with the fuel set to the bytes
remaining (`arr.size - q + 1`). A runtime clamp downgrades any non-advancing success to a
failure, so every self-*success* advances the offset; the productive nesting depth is
therefore bounded by the bytes remaining. A separate `Guarded` proof establishes that the
chosen fuel does not truncate acceptance for a particular body. Direct left recursion exhausts
the fuel and fails; arbitrary non-guarded bodies remain total but may be fuel-sensitive. This
replaces the `partial` loop the implementation once had; see
`grip-props/GripProps/FixComplete.lean`. -/

/-- Clamp a raw result so a success that did not advance past `q` becomes a failure at
`q`. This is what makes the `conditional` (`always`-consume) witness hold for `fix`
without unfolding the fuel recursion. -/
@[inline] def clampAdvance (arr : ByteArray) (q : Nat) : ParseResult α → ParseResult α
  | .ok x q' => if q < q' ∧ q' ≤ arr.size then .ok x q' else .error ⟨q, []⟩
  | .error e => .error e

/-- A raw result paired with the erased failure-position contract needed to expose it as a
`GParser` run. The subtype erases to its `ParseResult`; it exists only to let the structurally
recursive fuel approximation carry its induction hypothesis. -/
private abbrev BoundedResult (arr : ByteArray) (q : Nat) (α : Type) :=
  { r : ParseResult α // ∀ {e}, q ≤ arr.size → r = .error e →
      q ≤ e.pos ∧ e.pos ≤ arr.size }

private theorem clampAdvance_fwit {arr : ByteArray} {q : Nat} {r : ParseResult α}
    (hr : ∀ {e}, q ≤ arr.size → r = .error e → q ≤ e.pos ∧ e.pos ≤ arr.size)
    {e : Err} (hq : q ≤ arr.size) (h : clampAdvance arr q r = .error e) :
    q ≤ e.pos ∧ e.pos ≤ arr.size := by
  simp only [clampAdvance] at h
  split at h
  next a q' =>
    split at h
    · contradiction
    · simp only [ParseResult.error.injEq] at h
      subst e
      exact ⟨Nat.le_refl q, hq⟩
  next e' =>
    simp only [ParseResult.error.injEq] at h
    subst e
    exact hr hq rfl

/-- The recursive run, made total by a depth `fuel`. Each self-call spends one unit of fuel;
because the clamp forces every self-*success* to advance the offset, the productive nesting
depth is bounded by the bytes remaining. The `Guarded` hypothesis in
`grip-props/GripProps/FixComplete.lean` proves that the `arr.size - q + 1` budget does not
truncate a body's accepted parses. Fuel zero returns a failure; direct left recursion reaches
it, while other non-guarded bodies may vary with the supplied budget. -/
@[specialize] private def GParser.fixFuelBounded
    (f : GParser conditional α → GParser conditional α) :
    (n : Nat) → (arr : ByteArray) → (q : Nat) → BoundedResult arr q α
  | 0, _, q => ⟨.error ⟨q, []⟩, by
      intro e hq h
      simp only [ParseResult.error.injEq] at h
      subst e
      exact ⟨Nat.le_refl q, hq⟩⟩
  | n + 1, arr, q =>
  let self : GParser conditional α :=
    { run := fun a p => clampAdvance a p (GParser.fixFuelBounded f n a p).val
      cwit := by
        intro a p x p' h
        show p < p'
        simp only [clampAdvance] at h
        split at h
        · split at h
          · rename_i hg
            simp only [ParseResult.ok.injEq] at h
            omega
          · exact absurd h (by simp)
        · exact absurd h (by simp)
      ewit := by intro he; exact absurd he (by decide)
      swit := by intro he; exact absurd he (by decide)
      bwit := by
        intro a p x p' _hq h
        simp only [clampAdvance] at h
        split at h
        · split at h
          · rename_i hg
            simp only [ParseResult.ok.injEq] at h
            omega
          · exact absurd h (by simp)
        · exact absurd h (by simp)
      fwit := by
        intro a p e hp h
        exact clampAdvance_fwit (GParser.fixFuelBounded f n a p).property hp h }
  ⟨(f self).run arr q, by
    intro e hq h
    exact (f self).fwit hq h⟩

/-- The executable projection of `fixFuelBounded`. The bound proof is erased, so this remains
the same `Nat → ByteArray → Nat → ParseResult` runtime interface. -/
@[specialize] def GParser.fixFuel (f : GParser conditional α → GParser conditional α) :
    Nat → ByteArray → Nat → ParseResult α :=
  fun n arr q => (GParser.fixFuelBounded f n arr q).val

/-- Build a recursive `conditional` parser as the fixpoint of `f`. See the module note
above for the totality-not-productivity caveat. -/
@[specialize] def GParser.fix (f : GParser conditional α → GParser conditional α) :
    GParser conditional α where
  run arr q := clampAdvance arr q (GParser.fixFuel f (arr.size - q + 1) arr q)
  cwit := by
    intro arr q a q' h
    show q < q'
    simp only [clampAdvance] at h
    split at h
    · split at h
      · rename_i hg
        simp only [ParseResult.ok.injEq] at h
        omega
      · exact absurd h (by simp)
    · exact absurd h (by simp)
  ewit := by intro he; exact absurd he (by decide)
  swit := by intro he; exact absurd he (by decide)
  bwit := by
    intro arr q a q' _hq h
    simp only [clampAdvance] at h
    split at h
    · split at h
      · rename_i hg
        simp only [ParseResult.ok.injEq] at h
        omega
      · exact absurd h (by simp)
    · exact absurd h (by simp)
  fwit := by
    intro arr q e hq h
    exact clampAdvance_fwit
      (GParser.fixFuelBounded f (arr.size - q + 1) arr q).property hq h

/-- The clamped self-reference `fix` threads into the body at fuel level `n`: its recursive
run is `fixFuel f n` behind the advance clamp. Exposed (with unfolding lemmas below) so the
metatheory can reason about `fixFuel` without unfolding the anonymous inner structure; see
`grip-props/GripProps/FixComplete.lean`. -/
def GParser.fixSelf (f : GParser conditional α → GParser conditional α) (n : Nat) :
    GParser conditional α where
  run a p := clampAdvance a p (GParser.fixFuel f n a p)
  cwit := by
    intro a p x p' h
    show p < p'
    simp only [clampAdvance] at h
    split at h
    · split at h
      · rename_i hg
        simp only [ParseResult.ok.injEq] at h
        omega
      · exact absurd h (by simp)
    · exact absurd h (by simp)
  ewit := by intro he; exact absurd he (by decide)
  swit := by intro he; exact absurd he (by decide)
  bwit := by
    intro a p x p' _hq h
    simp only [clampAdvance] at h
    split at h
    · split at h
      · rename_i hg
        simp only [ParseResult.ok.injEq] at h
        omega
      · exact absurd h (by simp)
    · exact absurd h (by simp)
  fwit := by
    intro a p e hp h
    exact clampAdvance_fwit (GParser.fixFuelBounded f n a p).property hp h

/-- `fixSelf`'s run is the clamp of the lower-fuel `fixFuel`. -/
@[simp] theorem GParser.fixSelf_run (f : GParser conditional α → GParser conditional α)
    (n : Nat) (a : ByteArray) (p : Nat) :
    (GParser.fixSelf f n).run a p = clampAdvance a p (GParser.fixFuel f n a p) := rfl

/-- The one-step unfolding of `fixFuel`: at fuel `n+1`, run the body applied to the clamped
`fixSelf` at fuel `n`. -/
theorem GParser.fixFuel_succ (f : GParser conditional α → GParser conditional α)
    (n : Nat) (arr : ByteArray) (q : Nat) :
    GParser.fixFuel f (n + 1) arr q = (f (GParser.fixSelf f n)).run arr q := rfl

/-- Fuel zero fails at the current offset. -/
@[simp] theorem GParser.fixFuel_zero (f : GParser conditional α → GParser conditional α)
    (arr : ByteArray) (q : Nat) :
    GParser.fixFuel f 0 arr q = .error ⟨q, []⟩ := rfl

end Grip
