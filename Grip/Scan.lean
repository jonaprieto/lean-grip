/-
Copyright (c) 2026 Jonathan Cubides. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Cubides
-/

import Grip.Graded

/-!
# Grip.Scan -- total scanners and repetition

The looping combinators, all total (structural on `arr.size - q`) rather than `partial`.
The raw scan loops `scanFwd`/`foldFwd`/`natFwd` with their forward-progress lemmas, and
the parsers built on them: `takeWhile`/`takeWhile1`, `foldMany`/`many`, and `nat`. The
`@[specialize]` on each loop lets a statically-known predicate monomorphize into it. The
point combinators are in `Grip.Byte`; the graded type and `fix` in `Grip.Graded`.
-/

open Necessity
open Grade

namespace Grip

variable {g g' : Grade} {ge ge' gc gc' : Necessity} {α β : Type}

/-- Scan forward while `f` holds. Total -- structural on the measure
`arr.size - q` (each step advances one byte, bounded by `arr.size`). `@[specialize]` so
a known predicate (e.g. `Ascii.isWs`) is monomorphized into the loop rather than called
indirectly per byte. -/
@[specialize] def scanFwd (arr : ByteArray) (f : UInt8 → Bool) (q : Nat) : Nat :=
  if h : q < arr.size then (if f arr[q] then scanFwd arr f (q + 1) else q) else q
termination_by arr.size - q
decreasing_by omega

/-- `scanFwd` never rewinds. -/
theorem scanFwd_ge (arr : ByteArray) (f : UInt8 → Bool) (q : Nat) : q ≤ scanFwd arr f q := by
  rw [scanFwd]
  split
  · split
    · exact Nat.le_trans (Nat.le_succ q) (scanFwd_ge arr f (q + 1))
    · exact Nat.le_refl q
  · exact Nat.le_refl q
termination_by arr.size - q
decreasing_by omega

/-- With a leading matching byte, `scanFwd` strictly advances. -/
theorem scanFwd_gt (arr : ByteArray) (f : UInt8 → Bool) (q : Nat)
    (h : q < arr.size) (hf : f arr[q] = true) : q < scanFwd arr f q := by
  rw [scanFwd, dif_pos h, if_pos hf]
  exact Nat.lt_of_lt_of_le (Nat.lt_succ_self q) (scanFwd_ge arr f (q + 1))

/-- Scan while `f` holds, returning the number of bytes consumed.
Always succeeds (result is `.ok`). -/
@[inline] def GParser.takeWhile (f : UInt8 → Bool) : GParser flexible Nat where
  run := fun arr p => let q := scanFwd arr f p; .ok (q - p) q
  cwit := by
    intro arr q a q' heq
    simp only [ParseResult.ok.injEq] at heq
    obtain ⟨_, rfl⟩ := heq
    exact scanFwd_ge arr f q
  ewit := by intro he; exact absurd he (by decide)
  swit := by intro _ arr q; exact ⟨_, _, rfl⟩

/-- One-or-more bytes satisfying `f`.
On failure the furthest offset is the current position. -/
@[inline] def GParser.takeWhile1 (f : UInt8 → Bool) : GParser conditional Nat where
  run := fun arr p =>
    if h : p < arr.size then
      if f arr[p] then (GParser.takeWhile f).run arr p else .error ⟨p, []⟩
    else .error ⟨p, []⟩
  cwit := by
    intro arr q a q' heq
    split at heq
    · rename_i hbound
      split at heq
      · rename_i hf
        simp only [GParser.takeWhile, ParseResult.ok.injEq] at heq
        obtain ⟨_, rfl⟩ := heq
        exact scanFwd_gt arr f q hbound hf
      · exact absurd heq (by simp)
    · exact absurd heq (by simp)
  ewit := by intro he; exact absurd he (by decide)
  swit := by intro he; exact absurd he (by decide)

/-- Total repetition core: fold `p`'s results into `a`, advancing while `p` succeeds
and strictly consumes (in bounds). Total -- structural on `arr.size - q`; the
guard `q < q' ≤ arr.size` guarantees the measure drops. `@[specialize]` so the `step`
and the element parser fuse into the loop when they are statically known. -/
@[specialize] def foldFwd {ge : Necessity} {α β : Type} (step : β → α → β)
    (p : GParser ⟨ge, always⟩ α) (arr : ByteArray) (a : β) (q : Nat) : β × Nat :=
  match p.run arr q with
  | .ok x q' =>
    if _hq : q < q' ∧ q' ≤ arr.size then foldFwd step p arr (step a x) q' else (step a x, q')
  | .error _ => (a, q)
termination_by arr.size - q
decreasing_by (obtain ⟨h1, h2⟩ := _hq; omega)

/-- `foldFwd` never rewinds. -/
theorem foldFwd_ge {ge : Necessity} {α β : Type} (step : β → α → β) (p : GParser ⟨ge, always⟩ α)
    (arr : ByteArray) (a : β) (q : Nat) : q ≤ (foldFwd step p arr a q).2 := by
  rw [foldFwd]
  split
  next x q' hp =>
    have hlt : q < q' := p.cwit hp
    split
    · exact Nat.le_trans (Nat.le_of_lt hlt) (foldFwd_ge step p arr (step a x) q')
    · exact Nat.le_of_lt hlt
  next => exact Nat.le_refl q
termination_by arr.size - q
decreasing_by omega

/-- Fold `p` zero-or-more times into `acc` (no list). Total (see `foldFwd`).
Always succeeds (result is `.ok`). -/
@[inline] def GParser.foldMany (h : β → α → β) (acc : β) (p : GParser ⟨ge, always⟩ α) :
    GParser flexible β where
  run := fun arr pos => match foldFwd h p arr acc pos with | (b, q) => .ok b q
  cwit := by
    intro arr pos b q' heq
    simp only [ParseResult.ok.injEq] at heq
    have hge := foldFwd_ge h p arr acc pos
    obtain ⟨_, rfl⟩ := heq
    exact hge
  ewit := by intro he; exact absurd he (by decide)
  swit := by intro _ arr pos; exact ⟨_, _, rfl⟩

/-- Fold decimal digits into `acc`. Total -- structural on `arr.size - q`. -/
@[specialize] def natFwd (arr : ByteArray) (acc q : Nat) : Nat × Nat :=
  if h : q < arr.size then
    let b := arr[q]
    if 48 ≤ b && b ≤ 57 then natFwd arr (acc * 10 + (b.toNat - 48)) (q + 1) else (acc, q)
  else (acc, q)
termination_by arr.size - q
decreasing_by omega

/-- `natFwd` unfolded one step with the `let` inlined (so `split` sees the branch). -/
theorem natFwd_eq (arr : ByteArray) (acc q : Nat) :
    natFwd arr acc q =
      if h : q < arr.size then
        (if 48 ≤ arr[q] && arr[q] ≤ 57 then natFwd arr (acc * 10 + (arr[q].toNat - 48)) (q + 1)
         else (acc, q))
      else (acc, q) := by
  rw [natFwd]

/-- `natFwd` never rewinds. -/
theorem natFwd_ge (arr : ByteArray) (acc q : Nat) : q ≤ (natFwd arr acc q).2 := by
  rw [natFwd_eq]
  split
  next hbound =>
    split
    · exact Nat.le_trans (Nat.le_succ q) (natFwd_ge arr (acc * 10 + (arr[q].toNat - 48)) (q + 1))
    · exact Nat.le_refl q
  next => exact Nat.le_refl q
termination_by arr.size - q
decreasing_by omega

/-- With a leading digit, `natFwd` strictly advances. -/
theorem natFwd_gt (arr : ByteArray) (acc q : Nat) (h : q < arr.size)
    (hd : (48 ≤ arr[q] && arr[q] ≤ 57) = true) : q < (natFwd arr acc q).2 := by
  rw [natFwd_eq, dif_pos h, if_pos hd]
  exact Nat.lt_of_lt_of_le (Nat.lt_succ_self q)
    (natFwd_ge arr (acc * 10 + (arr[q].toNat - 48)) (q + 1))

/-- Parse a decimal natural number (one or more digits). Always consumes on success.
On failure the furthest offset is the current position. -/
@[inline] def GParser.nat : GParser conditional Nat where
  run := fun arr p0 =>
    if h : p0 < arr.size then
      let b := arr[p0]
      if 48 ≤ b && b ≤ 57 then (match natFwd arr 0 p0 with | (n, q) => .ok n q) else .error ⟨p0, []⟩
    else .error ⟨p0, []⟩
  cwit := by
    intro arr q a q' heq
    split at heq
    · rename_i hbound
      by_cases hd : (48 ≤ arr[q] && arr[q] ≤ 57) = true
      · have hgt := natFwd_gt arr 0 q hbound hd
        simp only [hd, if_true, ParseResult.ok.injEq] at heq
        obtain ⟨_, rfl⟩ := heq
        exact hgt
      · simp only [Bool.not_eq_true] at hd
        simp [hd] at heq
    · exact absurd heq (by simp)
  ewit := by intro he; exact absurd he (by decide)
  swit := by intro he; exact absurd he (by decide)

/-- Zero-or-more `p` (always-consuming) into a list. Total (via `foldFwd`).
Always succeeds (result is `.ok`). -/
@[inline] def GParser.many (p : GParser ⟨ge, always⟩ α) : GParser flexible (List α) where
  run := fun arr pos =>
    match foldFwd (fun acc x => x :: acc) p arr [] pos with
    | (xs, q) => .ok xs.reverse q
  cwit := by
    intro arr pos b q' heq
    have hge := foldFwd_ge (fun acc x => x :: acc) p arr ([] : List α) pos
    split at heq
    next xs q hfold =>
      simp only [ParseResult.ok.injEq] at heq
      obtain ⟨_, rfl⟩ := heq
      rw [hfold] at hge
      exact hge
  ewit := by intro he; exact absurd he (by decide)
  swit := by
    intro _ arr pos
    split
    next xs q _ => exact ⟨xs.reverse, q, rfl⟩

end Grip
