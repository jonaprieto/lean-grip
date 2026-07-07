/-
Copyright 2026 Jonathan Cubides. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Grip.Grade

/-!
# Grip.Graded — a compiled, byte-level graded parser backend

Shallow (combinators are `@[inline]` functions the Lean compiler fuses into the grammar),
over a raw `ByteArray` with `Nat` positions, results as `Option (α × Nat)` — no
reified tree, no boxed `Char`, no witness-carrying outcome at runtime.

The `Grade` index (error × consumption `Necessity`) is threaded through the
combinator types exactly as in a graded monad, so the same static discipline holds.

`GParser` carries three *erased* `Prop` witnesses tying the grade to runtime:
- `cwit` (a success advances the offset exactly as `consumes` claims),
- `ewit` (`always`-error never succeeds),
- `swit` (`never`-error always succeeds).

The witnesses erase, so `run` stays the bare `Option` fast path.

Ported from `prim-parser/PrimParser/Byte.lean` (lines 39-482). No mathlib.
-/

open Necessity
open Grade

namespace Grip

/-- A byte-level parser with static grade `g`, producing `α`. `run` returns the
value and the new byte offset, or `none` on failure.

The three `Prop` fields are the *grade soundness* witnesses; they are erased at
runtime (proof-irrelevant, carrying no data), so `run` is the whole runtime cost. -/
structure GParser (g : Grade) (α : Type) where
  /-- Run the parser at an offset, returning the value and new offset, or `none`. -/
  run : ByteArray → Nat → Option (α × Nat)
  /-- Consumption soundness: a successful parse advances the offset exactly as the
  grade's `consumes` component claims (`always ⇒ q<q'`, `possibly ⇒ q≤q'`,
  `never ⇒ q=q'`). -/
  cwit : ∀ {arr q a q'}, run arr q = some (a, q') → consumptionWitness q q' g.consumes
  /-- Error soundness, must-fail direction: a grade claiming `always`-error never
  succeeds. -/
  ewit : g.errors = always → ∀ arr q, run arr q = none
  /-- Error soundness, must-succeed direction: a grade claiming `never`-error always
  succeeds. -/
  swit : g.errors = never → ∀ arr q, (run arr q).isSome = true

variable {g g' : Grade} {ge ge' gc gc' : Necessity} {α β : Type}

/-! ### Grade-algebra witness helper lemmas -/

/-- Chain two consumption witnesses across a shared midpoint. -/
private theorem cw_seq {c0 c1 : Necessity} {q r s : Nat}
    (w0 : consumptionWitness q r c0) (w1 : consumptionWitness r s c1) :
    consumptionWitness q s (max c0 c1) := by
  have h := consumptionWitness.trans w1 w0
  rwa [Necessity.sup_comm] at h

/-- A success rules out the `always`-error grade (via `ewit`). -/
theorem GParser.errors_ne_always {g : Grade} {α} (p : GParser g α) {arr q a q'}
    (h : p.run arr q = some (a, q')) : g.errors ≠ always := fun he => by
  rw [p.ewit he arr q] at h; exact absurd h (by simp)

/-- A failure rules out the `never`-error grade (via `swit`). -/
theorem GParser.errors_ne_never {g : Grade} {α} (p : GParser g α) {arr q}
    (h : p.run arr q = none) : g.errors ≠ never := fun he => by
  have := p.swit he arr q; rw [h] at this; exact absurd this (by simp)

/-! ### Primitive combinators -/

/-- Consume nothing, never fail. -/
@[inline] def GParser.pure (a : α) : GParser 1 α where
  run := fun _ p => some (a, p)
  cwit := by intro arr q b q' h; simp only [Option.some.injEq, Prod.mk.injEq] at h; exact h.2
  ewit := by intro he; exact absurd he (by decide)
  swit := by intro _ _ _; rfl

/-- Always fail. -/
@[inline] def GParser.fail : GParser empty α where
  run := fun _ _ => none
  cwit := by intro arr q a q' h; exact absurd h (by simp)
  ewit := by intro _ _ _; rfl
  swit := by intro he; exact absurd he (by decide)

/-- Consume one byte satisfying `f`, or fail without consuming. -/
@[inline] def GParser.satisfy (f : UInt8 → Bool) : GParser conditional UInt8 where
  run := fun arr p => if h : p < arr.size then (if f arr[p] then some (arr[p], p + 1) else none) else none
  cwit := by
    intro arr q a q' heq
    split at heq
    · split at heq
      · injection heq with hpair; injection hpair with _ hq; omega
      · exact absurd heq (by simp)
    · exact absurd heq (by simp)
  ewit := by intro he; exact absurd he (by decide)
  swit := by intro he; exact absurd he (by decide)

/-- Match a specific byte. -/
@[inline] def GParser.byte (c : UInt8) : GParser conditional Unit where
  run := fun arr p => if h : p < arr.size then (if arr[p] == c then some ((), p + 1) else none) else none
  cwit := by
    intro arr q a q' heq
    split at heq
    · split at heq
      · injection heq with hpair; injection hpair with _ hq; omega
      · exact absurd heq (by simp)
    · exact absurd heq (by simp)
  ewit := by intro he; exact absurd he (by decide)
  swit := by intro he; exact absurd he (by decide)

/-- Map over the result (grade preserved). -/
@[inline] def GParser.map (h : α → β) (x : GParser g α) : GParser g β where
  run := fun arr p => (x.run arr p).map fun (a, p') => (h a, p')
  cwit := by
    intro arr q b q' heq
    rw [Option.map_eq_some_iff] at heq
    obtain ⟨⟨xa, p'⟩, hx, hb⟩ := heq
    obtain ⟨_, rfl⟩ : h xa = b ∧ p' = q' := by simpa using hb
    exact x.cwit hx
  ewit := by intro he arr q; simp [x.ewit he arr q]
  swit := by
    intro he arr q
    have hs := x.swit he arr q
    cases hx : x.run arr q with
    | none => rw [hx] at hs; simp at hs
    | some r => simp

/-- Sequence, keeping the right value; grades multiply. -/
@[inline] def GParser.seqR (x : GParser g α) (y : GParser g' β) : GParser (g * g') β where
  run := fun arr p => match x.run arr p with | some (_, p') => y.run arr p' | none => none
  cwit := by
    intro arr q a q' heq
    split at heq
    next fst p' hx => simpa only [grade_mul_consumes] using cw_seq (x.cwit hx) (y.cwit heq)
    next hx => exact absurd heq (by simp)
  ewit := by
    intro he arr q
    simp only [grade_mul_errors, Necessity.max_always] at he
    split
    next fst p' hx =>
      rcases he with he | he
      · rw [x.ewit he arr q] at hx; exact absurd hx (by simp)
      · exact y.ewit he arr p'
    next hx => rfl
  swit := by
    intro he arr q
    simp only [grade_mul_errors, Necessity.max_never] at he
    obtain ⟨he1, he2⟩ := he
    split
    next fst p' hx => exact y.swit he2 arr p'
    next hx => have := x.swit he1 arr q; rw [hx] at this; simp at this

/-- Sequence, keeping the left value; grades multiply. -/
@[inline] def GParser.seqL (x : GParser g α) (y : GParser g' β) : GParser (g * g') α where
  run := fun arr p => match x.run arr p with
    | some (a, p') => match y.run arr p' with | some (_, p'') => some (a, p'') | none => none
    | none => none
  cwit := by
    intro arr q a q' heq
    split at heq
    next fst p' hx =>
      split at heq
      next snd p'' hy =>
        simp only [Option.some.injEq, Prod.mk.injEq] at heq
        obtain ⟨_, rfl⟩ := heq
        simpa only [grade_mul_consumes] using cw_seq (x.cwit hx) (y.cwit hy)
      next hy => exact absurd heq (by simp)
    next hx => exact absurd heq (by simp)
  ewit := by
    intro he arr q
    simp only [grade_mul_errors, Necessity.max_always] at he
    split
    next fst p' hx =>
      rcases he with he | he
      · rw [x.ewit he arr q] at hx; exact absurd hx (by simp)
      · rw [y.ewit he arr p']
    next hx => rfl
  swit := by
    intro he arr q
    simp only [grade_mul_errors, Necessity.max_never] at he
    obtain ⟨he1, he2⟩ := he
    split
    next fst p' hx =>
      split
      next snd p'' hy => rfl
      next hy => have := y.swit he2 arr p'; rw [hy] at this; simp at this
    next hx => have := x.swit he1 arr q; rw [hx] at this; simp at this

/-- Ordered choice; grade follows `Grade.choice`. -/
@[inline] def GParser.alt (x : GParser ⟨ge, gc⟩ α) (y : GParser ⟨ge', gc'⟩ α) :
    GParser ⟨min ge ge', ge.ite gc' gc⟩ α where
  run := fun arr p => match x.run arr p with | some r => some r | none => y.run arr p
  cwit := by
    intro arr q a q' heq
    split at heq
    next r hx =>
      obtain rfl := Option.some.inj heq
      exact consumptionWitness.ite_left (le_possibly_of_ne_always (x.errors_ne_always hx)) (x.cwit hx)
    next hx =>
      exact consumptionWitness.ite_right (possibly_le_of_ne_never (x.errors_ne_never hx)) (y.cwit heq)
  ewit := by
    intro he arr q
    simp only [Necessity.min_always] at he
    obtain ⟨he1, he2⟩ := he
    split
    next r hx => rw [x.ewit he1 arr q] at hx; exact absurd hx (by simp)
    next hx => exact y.ewit he2 arr q
  swit := by
    intro he arr q
    simp only [Necessity.min_never] at he
    split
    next r hx => rfl
    next hx =>
      rcases he with hg | hg
      · have := x.swit hg arr q; rw [hx] at this; simp at this
      · exact y.swit hg arr q

/-! ### Scanners and repetition -/

/-- Scan forward while `f` holds. **Total** — structural on the measure
`arr.size - q` (each step advances one byte, bounded by `arr.size`). -/
def scanFwd (arr : ByteArray) (f : UInt8 → Bool) (q : Nat) : Nat :=
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

/-- Scan while `f` holds, returning the number of bytes consumed. -/
@[inline] def GParser.takeWhile (f : UInt8 → Bool) : GParser flexible Nat where
  run := fun arr p => let q := scanFwd arr f p; some (q - p, q)
  cwit := by
    intro arr q a q' heq
    simp only [Option.some.injEq, Prod.mk.injEq] at heq
    obtain ⟨_, rfl⟩ := heq
    exact scanFwd_ge arr f q
  ewit := by intro he; exact absurd he (by decide)
  swit := by intro _ _ _; rfl

/-- One-or-more bytes satisfying `f`. -/
@[inline] def GParser.takeWhile1 (f : UInt8 → Bool) : GParser conditional Nat where
  run := fun arr p =>
    if h : p < arr.size then
      if f arr[p] then (GParser.takeWhile f).run arr p else none
    else none
  cwit := by
    intro arr q a q' heq
    split at heq
    · rename_i hbound
      split at heq
      · rename_i hf
        simp only [GParser.takeWhile, Option.some.injEq, Prod.mk.injEq] at heq
        obtain ⟨_, rfl⟩ := heq
        exact scanFwd_gt arr f q hbound hf
      · exact absurd heq (by simp)
    · exact absurd heq (by simp)
  ewit := by intro he; exact absurd he (by decide)
  swit := by intro he; exact absurd he (by decide)

/-- Total repetition core: fold `p`'s results into `a`, advancing while `p` succeeds
and strictly consumes (in bounds). **Total** — structural on `arr.size - q`; the
guard `q < q' ≤ arr.size` guarantees the measure drops. -/
def foldFwd {ge : Necessity} {α β : Type} (step : β → α → β) (p : GParser ⟨ge, always⟩ α)
    (arr : ByteArray) (a : β) (q : Nat) : β × Nat :=
  match p.run arr q with
  | some (x, q') =>
    if _hq : q < q' ∧ q' ≤ arr.size then foldFwd step p arr (step a x) q' else (step a x, q')
  | none => (a, q)
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
  next hp => exact Nat.le_refl q
termination_by arr.size - q
decreasing_by omega

/-- Fold `p` zero-or-more times into `acc` (no list). Total (see `foldFwd`). -/
@[inline] def GParser.foldMany (h : β → α → β) (acc : β) (p : GParser ⟨ge, always⟩ α) :
    GParser flexible β where
  run := fun arr pos => some (foldFwd h p arr acc pos)
  cwit := by
    intro arr pos b q' heq
    have hge := foldFwd_ge h p arr acc pos
    rw [Option.some.inj heq] at hge
    exact hge
  ewit := by intro he; exact absurd he (by decide)
  swit := by intro _ _ _; rfl

/-- Monadic bind; grades multiply. -/
@[inline] def GParser.bind (x : GParser g α) (f : α → GParser g' β) : GParser (g * g') β where
  run := fun arr p => match x.run arr p with | some (a, p') => (f a).run arr p' | none => none
  cwit := by
    intro arr q a q' heq
    split at heq
    next fst p' hx => simpa only [grade_mul_consumes] using cw_seq (x.cwit hx) ((f fst).cwit heq)
    next hx => exact absurd heq (by simp)
  ewit := by
    intro he arr q
    simp only [grade_mul_errors, Necessity.max_always] at he
    split
    next fst p' hx =>
      rcases he with he | he
      · rw [x.ewit he arr q] at hx; exact absurd hx (by simp)
      · exact (f fst).ewit he arr p'
    next hx => rfl
  swit := by
    intro he arr q
    simp only [grade_mul_errors, Necessity.max_never] at he
    obtain ⟨he1, he2⟩ := he
    split
    next fst p' hx => exact (f fst).swit he2 arr p'
    next hx => have := x.swit he1 arr q; rw [hx] at this; simp at this

/-- Apply a binary function across two parses; grades multiply. -/
@[inline] def GParser.map2 {γ : Type} (f : α → β → γ) (x : GParser g α) (y : GParser g' β) :
    GParser (g * g') γ where
  run := fun arr p => match x.run arr p with
    | some (a, p') => match y.run arr p' with | some (b, p'') => some (f a b, p'') | none => none
    | none => none
  cwit := by
    intro arr q a q' heq
    split at heq
    next fst p' hx =>
      split at heq
      next snd p'' hy =>
        simp only [Option.some.injEq, Prod.mk.injEq] at heq
        obtain ⟨_, rfl⟩ := heq
        simpa only [grade_mul_consumes] using cw_seq (x.cwit hx) (y.cwit hy)
      next hy => exact absurd heq (by simp)
    next hx => exact absurd heq (by simp)
  ewit := by
    intro he arr q
    simp only [grade_mul_errors, Necessity.max_always] at he
    split
    next fst p' hx =>
      rcases he with he | he
      · rw [x.ewit he arr q] at hx; exact absurd hx (by simp)
      · rw [y.ewit he arr p']
    next hx => rfl
  swit := by
    intro he arr q
    simp only [grade_mul_errors, Necessity.max_never] at he
    obtain ⟨he1, he2⟩ := he
    split
    next fst p' hx =>
      split
      next snd p'' hy => rfl
      next hy => have := y.swit he2 arr p'; rw [hy] at this; simp at this
    next hx => have := x.swit he1 arr q; rw [hx] at this; simp at this

/-- Fold decimal digits into `acc`. **Total** — structural on `arr.size - q`. -/
def natFwd (arr : ByteArray) (acc q : Nat) : Nat × Nat :=
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
  exact Nat.lt_of_lt_of_le (Nat.lt_succ_self q) (natFwd_ge arr (acc * 10 + (arr[q].toNat - 48)) (q + 1))

/-- Parse a decimal natural number (one or more digits). Always consumes on success. -/
@[inline] def GParser.nat : GParser conditional Nat where
  run := fun arr p0 =>
    if h : p0 < arr.size then
      let b := arr[p0]; if 48 ≤ b && b ≤ 57 then some (natFwd arr 0 p0) else none
    else none
  cwit := by
    intro arr q a q' heq
    split at heq
    · rename_i hbound
      by_cases hd : (48 ≤ arr[q] && arr[q] ≤ 57) = true
      · have hgt := natFwd_gt arr 0 q hbound hd
        simp only [hd, if_true, Option.some.injEq] at heq
        rw [heq] at hgt
        exact hgt
      · simp only [Bool.not_eq_true] at hd
        simp [hd] at heq
    · exact absurd heq (by simp)
  ewit := by intro he; exact absurd he (by decide)
  swit := by intro he; exact absurd he (by decide)

/-- Consume exactly `n` bytes if available. -/
@[inline] def GParser.takeN (n : Nat) : GParser fallible Unit where
  run := fun arr p => if p + n ≤ arr.size then some ((), p + n) else none
  cwit := by
    intro arr q a q' heq
    split at heq
    · injection heq with hpair; injection hpair with _ hq; omega
    · exact absurd heq (by simp)
  ewit := by intro he; exact absurd he (by decide)
  swit := by intro he; exact absurd he (by decide)

/-- Zero-or-more `p` (always-consuming) into a list. Total (via `foldFwd`). -/
@[inline] def GParser.many (p : GParser ⟨ge, always⟩ α) : GParser flexible (List α) where
  run := fun arr pos => let (xs, q) := foldFwd (fun acc x => x :: acc) p arr [] pos; some (xs.reverse, q)
  cwit := by
    intro arr pos b q' heq
    have hge := foldFwd_ge (fun acc x => x :: acc) p arr ([] : List α) pos
    cases hfold : foldFwd (fun acc x => x :: acc) p arr ([] : List α) pos with
    | mk xs q =>
      simp only [Option.some.injEq, Prod.mk.injEq] at heq
      obtain ⟨_, rfl⟩ := heq
      exact hge
  ewit := by intro he; exact absurd he (by decide)
  swit := by intro _ _ _; rfl

/-- Parse a `ByteArray` from offset 0, returning only the value (no position). -/
@[inline] def GParser.parse (p : GParser g α) (arr : ByteArray) : Option α :=
  (p.run arr 0).map (·.1)

/-! ### Grade weakening -/

/-- Weaken a `GParser g α` to a less-precise grade `g'`.

Proofs required:
- `hc`: a success that satisfies `g.consumes` also satisfies `g'.consumes`
- `hew`: `g'.errors = always` implies `g.errors = always` (preserves must-fail)
- `hsw`: `g'.errors = never` implies `g.errors = never` (preserves must-succeed) -/
def GParser.weaken {g g' : Grade} (p : GParser g α)
    (hc : ∀ {n m : Nat}, consumptionWitness n m g.consumes → consumptionWitness n m g'.consumes)
    (hew : g'.errors = always → g.errors = always)
    (hsw : g'.errors = never → g.errors = never) : GParser g' α where
  run := p.run
  cwit := fun h => hc (p.cwit h)
  ewit := fun he => p.ewit (hew he)
  swit := fun he => p.swit (hsw he)

/-- Weaken any parser to `fallible` (errors = possibly, consumes = possibly),
losing all grade precision. Used by the ungraded `Parser` layer. -/
def GParser.weakenFallible {g : Grade} (p : GParser g α) : GParser fallible α :=
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

-- Example: a `conditional` parser weakened to `fallible` typechecks.
example (f : UInt8 → Bool) : GParser fallible UInt8 := GParser.weakenFallible (GParser.satisfy f)

end Grip

/-! ### Sanity: the graded byte backend parses. -/
section
open Grip

private def digits : GParser conditional Nat :=
  GParser.takeWhile1 (fun b => 48 ≤ b && b ≤ 57)

private def sample :=
  GParser.seqR (GParser.byte 40) (GParser.seqL digits (GParser.byte 41))  -- "(" digits ")"

#guard (GParser.parse digits "123".toUTF8) == some 3        -- 3 digit bytes consumed
#guard (GParser.parse sample "(42)".toUTF8) == some 2       -- 2 digit bytes inside parens
#guard (GParser.parse sample "(42".toUTF8) == none          -- missing ')'
#guard (GParser.parse (GParser.foldMany (· + ·) 0 digits) "".toUTF8) == some 0

end
