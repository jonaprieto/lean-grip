/-
Copyright (c) 2026 Jonathan Cubides. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Cubides
-/

import Grip.Graded

/-!
# Grip.Scan: total scanners and repetition

The looping combinators, all total (structural on `arr.size - q`) rather than `partial`.
The raw scan loops `scanFwd`/`foldFwd`/`natFwd` with their forward-progress lemmas, and
the parsers built on them: `takeWhile`/`takeWhile1`, `foldMany`/`many`, and `nat`. The
`@[specialize]` on each loop lets a statically-known predicate monomorphize into it. The
point combinators are in `Grip.Byte`; the graded type and `fix` in `Grip.Graded`.
-/

open Modality
open Grade

namespace Grip

variable {g g' : Grade} {ge ge' gc gc' : Modality} {α β : Type}

/-- Scan forward while `f` holds. Total: structural on the measure
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

/-- `scanFwd` stays within bounds when it starts within bounds. -/
theorem scanFwd_le (arr : ByteArray) (f : UInt8 → Bool) (q : Nat) (hq : q ≤ arr.size) :
    scanFwd arr f q ≤ arr.size := by
  rw [scanFwd]
  split
  · rename_i hlt
    split
    · exact scanFwd_le arr f (q + 1) hlt
    · exact hq
  · exact hq
termination_by arr.size - q
decreasing_by omega

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
  bwit := by
    intro arr q a q' hq heq
    simp only [ParseResult.ok.injEq] at heq
    obtain ⟨_, rfl⟩ := heq
    exact scanFwd_le arr f q hq

/-- Scan a JSON-style string body: advance until an *unescaped* `"` (0x22), treating a
backslash (0x5c) as an escape that consumes the next byte too. Total: structural on
`arr.size - q`. -/
@[specialize] def scanStrFwd (arr : ByteArray) (q : Nat) : Nat :=
  if h : q < arr.size then
    if arr[q] == 34 then q                                     -- unescaped `"`: stop
    else if arr[q] == 92 then
      (if q + 1 < arr.size then scanStrFwd arr (q + 2) else q + 1)  -- `\`: skip escaped byte
    else scanStrFwd arr (q + 1)
  else q
termination_by arr.size - q
decreasing_by all_goals omega

/-- `scanStrFwd` never rewinds. -/
theorem scanStrFwd_ge (arr : ByteArray) (q : Nat) : q ≤ scanStrFwd arr q := by
  rw [scanStrFwd]
  split
  · rename_i h
    split
    · exact Nat.le_refl q
    · split
      · split
        · have := scanStrFwd_ge arr (q + 2); omega
        · omega
      · have := scanStrFwd_ge arr (q + 1); omega
  · exact Nat.le_refl q
termination_by arr.size - q
decreasing_by all_goals omega

/-- `scanStrFwd` stays within bounds when it starts within bounds. -/
theorem scanStrFwd_le (arr : ByteArray) (q : Nat) (hq : q ≤ arr.size) :
    scanStrFwd arr q ≤ arr.size := by
  rw [scanStrFwd]
  split
  · rename_i h
    split
    · exact hq
    · split
      · split
        · have := scanStrFwd_le arr (q + 2) (by omega); omega
        · omega
      · have := scanStrFwd_le arr (q + 1) (by omega); omega
  · exact hq
termination_by arr.size - q
decreasing_by all_goals omega

/-- Scan a JSON string body (escape-aware), returning the number of bytes consumed.
Always succeeds (result is `.ok`). Pair with a `"` on each side for a full string literal. -/
@[inline] def GParser.takeStringBody : GParser flexible Nat where
  run := fun arr p => let q := scanStrFwd arr p; .ok (q - p) q
  cwit := by
    intro arr q a q' heq
    simp only [ParseResult.ok.injEq] at heq
    obtain ⟨_, rfl⟩ := heq
    exact scanStrFwd_ge arr q
  ewit := by intro he; exact absurd he (by decide)
  swit := by intro _ arr q; exact ⟨_, _, rfl⟩
  bwit := by
    intro arr q a q' hq heq
    simp only [ParseResult.ok.injEq] at heq
    obtain ⟨_, rfl⟩ := heq
    exact scanStrFwd_le arr q hq

/-- Hex digit byte: `0-9`, `a-f`, `A-F`. Local so `Scan` need not import `Ascii`. -/
@[inline] def isHexByte (b : UInt8) : Bool :=
  (48 ≤ b && b ≤ 57) || (97 ≤ b && b ≤ 102) || (65 ≤ b && b ≤ 70)

/-- Scan a *strict* RFC-8259 string body: from just after the opening `"` at `q`, advance to
and past the closing `"`, validating escapes. Returns `some end` (just past the closing quote)
on a well-formed body, or `none` on a malformed one: an unescaped control byte (`< 0x20`), an
unknown `\`-escape, a `\u` not followed by four hex digits, or end of input before the closing
quote. Total (structural on `arr.size - q`). Unlike `scanStrFwd`, this *validates* and can
reject, so the parser built on it is `conditional`, not `flexible`. -/
@[specialize] def scanStrBody (arr : ByteArray) (q : Nat) : Option Nat :=
  if h : q < arr.size then
    if arr[q] == 34 then some (q + 1)                                    -- closing `"`
    else if arr[q] == 92 then                                           -- `\` escape
      if h1 : q + 1 < arr.size then
        if arr[q + 1] == 34 || arr[q + 1] == 92 || arr[q + 1] == 47 || arr[q + 1] == 98
            || arr[q + 1] == 102 || arr[q + 1] == 110 || arr[q + 1] == 114
            || arr[q + 1] == 116 then
          scanStrBody arr (q + 2)                                       -- `\" \\ \/ \b \f \n \r \t`
        else if arr[q + 1] == 117 then                                  -- `\uXXXX`
          if h2 : q + 5 < arr.size then
            if isHexByte arr[q + 2] && isHexByte arr[q + 3] && isHexByte arr[q + 4]
                && isHexByte arr[q + 5] then
              scanStrBody arr (q + 6)
            else none
          else none
        else none
      else none
    else if arr[q] < 32 then none                                       -- unescaped control byte
    else scanStrBody arr (q + 1)                                        -- ordinary byte (opaque)
  else none                                                             -- ran off end, no close
termination_by arr.size - q
decreasing_by all_goals omega

/-- A successful `scanStrBody` never rewinds. -/
theorem scanStrBody_ge (arr : ByteArray) (q q' : Nat) (h : scanStrBody arr q = some q') :
    q ≤ q' := by
  rw [scanStrBody] at h
  split at h
  · split at h
    · simp only [Option.some.injEq] at h; omega
    · split at h
      · split at h
        · split at h
          · have := scanStrBody_ge arr (q + 2) q' h; omega
          · split at h
            · split at h
              · split at h
                · have := scanStrBody_ge arr (q + 6) q' h; omega
                · exact absurd h (by simp)
              · exact absurd h (by simp)
            · exact absurd h (by simp)
        · exact absurd h (by simp)
      · split at h
        · exact absurd h (by simp)
        · have := scanStrBody_ge arr (q + 1) q' h; omega
  · exact absurd h (by simp)
termination_by arr.size - q
decreasing_by all_goals omega

/-- A successful `scanStrBody` stays within bounds. -/
theorem scanStrBody_le (arr : ByteArray) (q q' : Nat) (h : scanStrBody arr q = some q') :
    q' ≤ arr.size := by
  rw [scanStrBody] at h
  split at h
  · rename_i hq
    split at h
    · simp only [Option.some.injEq] at h; omega
    · split at h
      · split at h
        · split at h
          · exact scanStrBody_le arr (q + 2) q' h
          · split at h
            · split at h
              · split at h
                · exact scanStrBody_le arr (q + 6) q' h
                · exact absurd h (by simp)
              · exact absurd h (by simp)
            · exact absurd h (by simp)
        · exact absurd h (by simp)
      · split at h
        · exact absurd h (by simp)
        · exact scanStrBody_le arr (q + 1) q' h
  · exact absurd h (by simp)
termination_by arr.size - q
decreasing_by all_goals omega

/-- Scan a strict JSON string literal starting at the opening `"`: `some end` (past the
closing `"`) or `none`. -/
@[inline] def scanStrLit (arr : ByteArray) (q : Nat) : Option Nat :=
  if h : q < arr.size then (if arr[q] == 34 then scanStrBody arr (q + 1) else none) else none

/-- A successful `scanStrLit` strictly advances (it consumes the opening quote). -/
theorem scanStrLit_gt (arr : ByteArray) (q q' : Nat) (h : scanStrLit arr q = some q') :
    q < q' := by
  rw [scanStrLit] at h
  split at h
  · split at h
    · have := scanStrBody_ge arr (q + 1) q' h; omega
    · exact absurd h (by simp)
  · exact absurd h (by simp)

/-- A successful `scanStrLit` stays within bounds. -/
theorem scanStrLit_le (arr : ByteArray) (q q' : Nat) (h : scanStrLit arr q = some q') :
    q' ≤ arr.size := by
  rw [scanStrLit] at h
  split at h
  · split at h
    · exact scanStrBody_le arr (q + 1) q' h
    · exact absurd h (by simp)
  · exact absurd h (by simp)

/-- A validated JSON string literal `"..."` in one scan, returning the number of bytes
consumed (both quotes included). Fails on a malformed literal (see `scanStrBody`). This is the
strict, single-pass counterpart to `byteC '"' *> takeStringBody *> byteC '"'`: it validates
escapes and rejects control bytes without per-byte combinator dispatch. On failure the furthest
offset is the current position. -/
@[inline] def GParser.stringLit : GParser conditional Nat where
  run := fun arr p =>
    match scanStrLit arr p with
    | some q => .ok (q - p) q
    | none   => .error ⟨p, []⟩
  cwit := by
    intro arr q a q' heq
    split at heq
    next k hk =>
      simp only [ParseResult.ok.injEq] at heq
      obtain ⟨_, rfl⟩ := heq
      exact scanStrLit_gt arr q k hk
    next => exact absurd heq (by simp)
  ewit := by intro he; exact absurd he (by decide)
  swit := by intro he; exact absurd he (by decide)
  bwit := by
    intro arr q a q' _hq heq
    split at heq
    next k hk =>
      simp only [ParseResult.ok.injEq] at heq
      obtain ⟨_, rfl⟩ := heq
      exact scanStrLit_le arr q k hk
    next => exact absurd heq (by simp)

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
  bwit := by
    intro arr q a q' hq heq
    split at heq
    · rename_i hbound
      split at heq
      · rename_i hf
        simp only [GParser.takeWhile, ParseResult.ok.injEq] at heq
        obtain ⟨_, rfl⟩ := heq
        exact scanFwd_le arr f q hq
      · exact absurd heq (by simp)
    · exact absurd heq (by simp)

/-- Total repetition core: fold `p`'s results into `a`, advancing while `p` succeeds
and strictly consumes (in bounds). Total: structural on `arr.size - q`; the
guard `q < q' ≤ arr.size` guarantees the measure drops. `@[specialize]` so the `step`
and the element parser fuse into the loop when they are statically known. -/
@[specialize] def foldFwd {ge : Modality} {α β : Type} (step : β → α → β)
    (p : GParser ⟨ge, always⟩ α) (arr : ByteArray) (a : β) (q : Nat) : β × Nat :=
  match p.run arr q with
  | .ok x q' =>
    if _hq : q < q' ∧ q' ≤ arr.size then foldFwd step p arr (step a x) q' else (step a x, q')
  | .error _ => (a, q)
termination_by arr.size - q
decreasing_by (obtain ⟨h1, h2⟩ := _hq; omega)

/-- `foldFwd` never rewinds. -/
theorem foldFwd_ge {ge : Modality} {α β : Type} (step : β → α → β) (p : GParser ⟨ge, always⟩ α)
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

/-- `foldFwd` stays within bounds when it starts within bounds (using the element's `bwit`). -/
theorem foldFwd_le {ge : Modality} {α β : Type} (step : β → α → β) (p : GParser ⟨ge, always⟩ α)
    (arr : ByteArray) (a : β) (q : Nat) (hq : q ≤ arr.size) :
    (foldFwd step p arr a q).2 ≤ arr.size := by
  rw [foldFwd]
  split
  next x q' hp =>
    have hlt : q < q' := p.cwit hp
    have hb : q' ≤ arr.size := p.bwit hq hp
    split
    · exact foldFwd_le step p arr (step a x) q' hb
    · exact hb
  next => exact hq
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
  bwit := by
    intro arr pos b q' hq heq
    simp only [ParseResult.ok.injEq] at heq
    have hle := foldFwd_le h p arr acc pos hq
    obtain ⟨_, rfl⟩ := heq
    exact hle

/-- Fold decimal digits into `acc`. Total: structural on `arr.size - q`. -/
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

/-- `natFwd` stays within bounds when it starts within bounds. -/
theorem natFwd_le (arr : ByteArray) (acc q : Nat) (hq : q ≤ arr.size) :
    (natFwd arr acc q).2 ≤ arr.size := by
  rw [natFwd_eq]
  split
  next hbound =>
    split
    · exact natFwd_le arr (acc * 10 + (arr[q].toNat - 48)) (q + 1) hbound
    · exact hq
  next => exact hq
termination_by arr.size - q
decreasing_by omega

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
  bwit := by
    intro arr q a q' hq heq
    split at heq
    · rename_i hbound
      by_cases hd : (48 ≤ arr[q] && arr[q] ≤ 57) = true
      · have hle := natFwd_le arr 0 q hq
        simp only [hd, if_true, ParseResult.ok.injEq] at heq
        obtain ⟨_, rfl⟩ := heq
        exact hle
      · simp only [Bool.not_eq_true] at hd
        simp [hd] at heq
    · exact absurd heq (by simp)

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
  bwit := by
    intro arr pos b q' hq heq
    have hle := foldFwd_le (fun acc x => x :: acc) p arr ([] : List α) pos hq
    split at heq
    next xs q hfold =>
      simp only [ParseResult.ok.injEq] at heq
      obtain ⟨_, rfl⟩ := heq
      rw [hfold] at hle
      exact hle

end Grip
