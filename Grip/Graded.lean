/-
Copyright 2026 Jonathan Cubides. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Grip.Grade

/-!
# Grip.Graded — a compiled, byte-level graded parser backend

Shallow (combinators are `@[inline]` functions the Lean compiler fuses into the grammar),
over a raw `ByteArray` with `Nat` positions, results as `Except Nat (α × Nat)` — no
reified tree, no boxed `Char`, no witness-carrying outcome at runtime.

The `Grade` index (error × consumption `Necessity`) is threaded through the
combinator types exactly as in a graded monad, so the same static discipline holds.

`GParser` carries three *erased* `Prop` witnesses tying the grade to runtime:
- `cwit` (a success advances the offset exactly as `consumes` claims),
- `ewit` (`always`-error never succeeds — every input yields an `.error k` at some
  furthest offset `k`),
- `swit` (`never`-error always succeeds — every input yields `.ok (a, q')`).

The witnesses erase, so `run` stays the bare `Except` fast path.  The offset in
`.error k` records the furthest byte position any attempted branch reached, enabling
precise error reporting without a second pass.

Ported from `prim-parser/PrimParser/Byte.lean` (lines 39-482). No mathlib.
-/

open Necessity
open Grade

namespace Grip

/-- A byte-level parser with static grade `g`, producing `α`. `run` returns
`.ok (value, new_offset)` on success, or `.error k` on failure where `k` is the
furthest byte offset any attempted branch reached.

The three `Prop` fields are the *grade soundness* witnesses; they are erased at
runtime (proof-irrelevant, carrying no data), so `run` is the whole runtime cost. -/
structure GParser (g : Grade) (α : Type) where
  /-- Run the parser at an offset, returning `.ok (value, new_offset)` on success
  or `.error k` on failure where `k` is the furthest byte offset reached. -/
  run : ByteArray → Nat → Except Nat (α × Nat)
  /-- Consumption soundness: a successful parse advances the offset exactly as the
  grade's `consumes` component claims (`always ⇒ q<q'`, `possibly ⇒ q≤q'`,
  `never ⇒ q=q'`). -/
  cwit : ∀ {arr q a q'}, run arr q = .ok (a, q') → consumptionWitness q q' g.consumes
  /-- Error soundness, must-fail direction: a grade claiming `always`-error never
  succeeds — for every input there exists a furthest failure offset `k`. -/
  ewit : g.errors = always → ∀ arr q, ∃ k, run arr q = .error k
  /-- Error soundness, must-succeed direction: a grade claiming `never`-error always
  succeeds — for every input there exist a value `a` and next offset `q'`. -/
  swit : g.errors = never → ∀ arr q, ∃ a q', run arr q = .ok (a, q')

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
    (h : p.run arr q = .ok (a, q')) : g.errors ≠ always := fun he => by
  obtain ⟨k, hk⟩ := p.ewit he arr q
  rw [hk] at h; exact absurd h (by simp)

/-- A failure rules out the `never`-error grade (via `swit`). -/
theorem GParser.errors_ne_never {g : Grade} {α} (p : GParser g α) {arr q k}
    (h : p.run arr q = .error k) : g.errors ≠ never := fun he => by
  obtain ⟨a, q', ha⟩ := p.swit he arr q
  rw [ha] at h; exact absurd h (by simp)

/-! ### Primitive combinators -/

/-- Consume nothing, never fail. -/
@[inline] def GParser.pure (a : α) : GParser 1 α where
  run := fun _ p => .ok (a, p)
  cwit := by
    intro arr q b q' h
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    exact h.2
  ewit := by intro he; exact absurd he (by decide)
  swit := by intro _ arr q; exact ⟨a, q, rfl⟩

/-- Always fail, recording the current position as the furthest offset reached. -/
@[inline] def GParser.fail : GParser empty α where
  run := fun _ p => .error p
  cwit := by intro arr q a q' h; exact absurd h (by simp)
  ewit := by intro _ arr q; exact ⟨q, rfl⟩
  swit := by intro he; exact absurd he (by decide)

/-- Consume one byte satisfying `f`, or fail without consuming.
On failure the furthest offset is the current position `p`. -/
@[inline] def GParser.satisfy (f : UInt8 → Bool) : GParser conditional UInt8 where
  run := fun arr p =>
    if h : p < arr.size then
      (if f arr[p] then .ok (arr[p], p + 1) else .error p)
    else .error p
  cwit := by
    intro arr q a q' heq
    split at heq
    · split at heq
      · simp only [Except.ok.injEq, Prod.mk.injEq] at heq; omega
      · exact absurd heq (by simp)
    · exact absurd heq (by simp)
  ewit := by intro he; exact absurd he (by decide)
  swit := by intro he; exact absurd he (by decide)

/-- Match a specific byte.
On failure the furthest offset is the current position `p`. -/
@[inline] def GParser.byte (c : UInt8) : GParser conditional Unit where
  run := fun arr p =>
    if h : p < arr.size then
      (if arr[p] == c then .ok ((), p + 1) else .error p)
    else .error p
  cwit := by
    intro arr q a q' heq
    split at heq
    · split at heq
      · simp only [Except.ok.injEq, Prod.mk.injEq] at heq; omega
      · exact absurd heq (by simp)
    · exact absurd heq (by simp)
  ewit := by intro he; exact absurd he (by decide)
  swit := by intro he; exact absurd he (by decide)

/-- Map over the result (grade preserved). -/
@[inline] def GParser.map (h : α → β) (x : GParser g α) : GParser g β where
  run := fun arr p =>
    match x.run arr p with
    | .ok (a, p') => .ok (h a, p')
    | .error k    => .error k
  cwit := by
    intro arr q b q' heq
    split at heq
    next a p' hx =>
      simp only [Except.ok.injEq, Prod.mk.injEq] at heq
      obtain ⟨_, rfl⟩ := heq
      exact x.cwit hx
    next k hx => exact absurd heq (by simp)
  ewit := by
    intro he arr q
    obtain ⟨k, hk⟩ := x.ewit he arr q
    exact ⟨k, by simp only [hk]⟩
  swit := by
    intro he arr q
    obtain ⟨a, q', ha⟩ := x.swit he arr q
    exact ⟨h a, q', by simp only [ha]⟩

/-- Sequence, keeping the right value; grades multiply.
Furthest offset from either `x` or `y` propagates on failure. -/
@[inline] def GParser.seqR (x : GParser g α) (y : GParser g' β) : GParser (g * g') β where
  run := fun arr p =>
    match x.run arr p with
    | .ok (_, p') => y.run arr p'
    | .error k    => .error k
  cwit := by
    intro arr q a q' heq
    split at heq
    next fst p' hx =>
      simpa only [grade_mul_consumes] using cw_seq (x.cwit hx) (y.cwit heq)
    next k hx => exact absurd heq (by simp)
  ewit := by
    intro he arr q
    simp only [grade_mul_errors, Necessity.max_always] at he
    rcases he with he | he
    · obtain ⟨k, hk⟩ := x.ewit he arr q
      exact ⟨k, by simp only [hk]⟩
    · cases hx : x.run arr q with
      | ok r =>
        obtain ⟨_, p'⟩ := r
        obtain ⟨k, hk⟩ := y.ewit he arr p'
        exact ⟨k, hk⟩
      | error k => exact ⟨k, rfl⟩
  swit := by
    intro he arr q
    simp only [grade_mul_errors, Necessity.max_never] at he
    obtain ⟨he1, he2⟩ := he
    cases hx : x.run arr q with
    | ok r =>
      obtain ⟨c, p'⟩ := r
      obtain ⟨a, q', ha⟩ := y.swit he2 arr p'
      exact ⟨a, q', ha⟩
    | error k =>
      obtain ⟨a, q', ha⟩ := x.swit he1 arr q
      rw [ha] at hx; exact absurd hx (by simp)

/-- Sequence, keeping the left value; grades multiply.
Furthest offset propagates on failure. -/
@[inline] def GParser.seqL (x : GParser g α) (y : GParser g' β) : GParser (g * g') α where
  run := fun arr p =>
    match x.run arr p with
    | .ok (a, p') =>
      match y.run arr p' with
      | .ok (_, p'') => .ok (a, p'')
      | .error k     => .error k
    | .error k => .error k
  cwit := by
    intro arr q a q' heq
    split at heq
    next fst p' hx =>
      split at heq
      next snd p'' hy =>
        simp only [Except.ok.injEq, Prod.mk.injEq] at heq
        obtain ⟨_, rfl⟩ := heq
        simpa only [grade_mul_consumes] using cw_seq (x.cwit hx) (y.cwit hy)
      next k hy => exact absurd heq (by simp)
    next k hx => exact absurd heq (by simp)
  ewit := by
    intro he arr q
    simp only [grade_mul_errors, Necessity.max_always] at he
    rcases he with he | he
    · obtain ⟨k, hk⟩ := x.ewit he arr q
      exact ⟨k, by simp only [hk]⟩
    · cases hx : x.run arr q with
      | ok r =>
        obtain ⟨_, p'⟩ := r
        obtain ⟨k, hk⟩ := y.ewit he arr p'
        exact ⟨k, by simp only [hk]⟩
      | error k => exact ⟨k, rfl⟩
  swit := by
    intro he arr q
    simp only [grade_mul_errors, Necessity.max_never] at he
    obtain ⟨he1, he2⟩ := he
    cases hx : x.run arr q with
    | ok r =>
      obtain ⟨a, p'⟩ := r
      cases hy : y.run arr p' with
      | ok s =>
        obtain ⟨_, p''⟩ := s
        exact ⟨a, p'', by simp only [hy]⟩
      | error k =>
        obtain ⟨b, q'', hb⟩ := y.swit he2 arr p'
        rw [hb] at hy; exact absurd hy (by simp)
    | error k =>
      obtain ⟨a, q', ha⟩ := x.swit he1 arr q
      rw [ha] at hx; exact absurd hx (by simp)

/-- Ordered choice; grade follows `Grade.choice`.
On failure, `.error (max kx ky)` records the furthest offset either branch reached
(megaparsec-style furthest-failure merge). -/
@[inline] def GParser.alt (x : GParser ⟨ge, gc⟩ α) (y : GParser ⟨ge', gc'⟩ α) :
    GParser ⟨min ge ge', ge.ite gc' gc⟩ α where
  run := fun arr p =>
    match x.run arr p with
    | .ok r  => .ok r
    | .error kx =>
      match y.run arr p with
      | .ok r  => .ok r
      | .error ky => .error (max kx ky)
  cwit := by
    intro arr q a q' heq
    split at heq
    · -- x succeeded
      rename_i r hx
      obtain rfl : r = (a, q') := Except.ok.inj heq
      exact consumptionWitness.ite_left
        (le_possibly_of_ne_always (x.errors_ne_always hx)) (x.cwit hx)
    · -- x failed; try y
      rename_i kx hx
      split at heq
      · rename_i r hy
        obtain rfl : r = (a, q') := Except.ok.inj heq
        exact consumptionWitness.ite_right
          (possibly_le_of_ne_never (x.errors_ne_never hx)) (y.cwit hy)
      · exact absurd heq (by simp)
  ewit := by
    intro he arr q
    simp only [Necessity.min_always] at he
    obtain ⟨he1, he2⟩ := he
    cases hx : x.run arr q with
    | ok r =>
      obtain ⟨k, hk⟩ := x.ewit he1 arr q
      rw [hk] at hx; exact absurd hx (by simp)
    | error kx =>
      obtain ⟨k, hk⟩ := y.ewit he2 arr q
      exact ⟨max kx k, by simp only [hk]⟩
  swit := by
    intro he arr q
    simp only [Necessity.min_never] at he
    cases hx : x.run arr q with
    | ok r =>
      obtain ⟨a, q'⟩ := r
      exact ⟨a, q', rfl⟩
    | error kx =>
      cases hy : y.run arr q with
      | ok r =>
        obtain ⟨a, q'⟩ := r
        exact ⟨a, q', rfl⟩
      | error ky =>
        rcases he with hg | hg
        · obtain ⟨a, q', ha⟩ := x.swit hg arr q
          rw [ha] at hx; exact absurd hx (by simp)
        · obtain ⟨a, q', ha⟩ := y.swit hg arr q
          rw [ha] at hy; exact absurd hy (by simp)

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

/-- Scan while `f` holds, returning the number of bytes consumed.
Always succeeds (result is `.ok`). -/
@[inline] def GParser.takeWhile (f : UInt8 → Bool) : GParser flexible Nat where
  run := fun arr p => let q := scanFwd arr f p; .ok (q - p, q)
  cwit := by
    intro arr q a q' heq
    simp only [Except.ok.injEq, Prod.mk.injEq] at heq
    obtain ⟨_, rfl⟩ := heq
    exact scanFwd_ge arr f q
  ewit := by intro he; exact absurd he (by decide)
  swit := by intro _ arr q; exact ⟨_, _, rfl⟩

/-- One-or-more bytes satisfying `f`.
On failure the furthest offset is the current position. -/
@[inline] def GParser.takeWhile1 (f : UInt8 → Bool) : GParser conditional Nat where
  run := fun arr p =>
    if h : p < arr.size then
      if f arr[p] then (GParser.takeWhile f).run arr p else .error p
    else .error p
  cwit := by
    intro arr q a q' heq
    split at heq
    · rename_i hbound
      split at heq
      · rename_i hf
        simp only [GParser.takeWhile, Except.ok.injEq, Prod.mk.injEq] at heq
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
  | .ok (x, q') =>
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
  run := fun arr pos => .ok (foldFwd h p arr acc pos)
  cwit := by
    intro arr pos b q' heq
    simp only [Except.ok.injEq] at heq
    have hge := foldFwd_ge h p arr acc pos
    rw [heq] at hge
    exact hge
  ewit := by intro he; exact absurd he (by decide)
  swit := by intro _ arr pos; exact ⟨_, _, rfl⟩

/-- Monadic bind; grades multiply.
Furthest offset propagates on failure. -/
@[inline] def GParser.bind (x : GParser g α) (f : α → GParser g' β) : GParser (g * g') β where
  run := fun arr p =>
    match x.run arr p with
    | .ok (a, p') => (f a).run arr p'
    | .error k    => .error k
  cwit := by
    intro arr q a q' heq
    split at heq
    next fst p' hx =>
      simpa only [grade_mul_consumes] using cw_seq (x.cwit hx) ((f fst).cwit heq)
    next k hx => exact absurd heq (by simp)
  ewit := by
    intro he arr q
    simp only [grade_mul_errors, Necessity.max_always] at he
    rcases he with he | he
    · obtain ⟨k, hk⟩ := x.ewit he arr q
      exact ⟨k, by simp only [hk]⟩
    · cases hx : x.run arr q with
      | ok r =>
        obtain ⟨fst, p'⟩ := r
        obtain ⟨k, hk⟩ := (f fst).ewit he arr p'
        exact ⟨k, hk⟩
      | error k => exact ⟨k, rfl⟩
  swit := by
    intro he arr q
    simp only [grade_mul_errors, Necessity.max_never] at he
    obtain ⟨he1, he2⟩ := he
    cases hx : x.run arr q with
    | ok r =>
      obtain ⟨fst, p'⟩ := r
      obtain ⟨a, q', ha⟩ := (f fst).swit he2 arr p'
      exact ⟨a, q', ha⟩
    | error k =>
      obtain ⟨a, q', ha⟩ := x.swit he1 arr q
      rw [ha] at hx; exact absurd hx (by simp)

/-- Apply a binary function across two parses; grades multiply.
Furthest offset propagates on failure. -/
@[inline] def GParser.map2 {γ : Type} (f : α → β → γ) (x : GParser g α) (y : GParser g' β) :
    GParser (g * g') γ where
  run := fun arr p =>
    match x.run arr p with
    | .ok (a, p') =>
      match y.run arr p' with
      | .ok (b, p'') => .ok (f a b, p'')
      | .error k     => .error k
    | .error k => .error k
  cwit := by
    intro arr q a q' heq
    split at heq
    next fst p' hx =>
      split at heq
      next snd p'' hy =>
        simp only [Except.ok.injEq, Prod.mk.injEq] at heq
        obtain ⟨_, rfl⟩ := heq
        simpa only [grade_mul_consumes] using cw_seq (x.cwit hx) (y.cwit hy)
      next k hy => exact absurd heq (by simp)
    next k hx => exact absurd heq (by simp)
  ewit := by
    intro he arr q
    simp only [grade_mul_errors, Necessity.max_always] at he
    rcases he with he | he
    · obtain ⟨k, hk⟩ := x.ewit he arr q
      exact ⟨k, by simp only [hk]⟩
    · cases hx : x.run arr q with
      | ok r =>
        obtain ⟨_, p'⟩ := r
        obtain ⟨k, hk⟩ := y.ewit he arr p'
        exact ⟨k, by simp only [hk]⟩
      | error k => exact ⟨k, rfl⟩
  swit := by
    intro he arr q
    simp only [grade_mul_errors, Necessity.max_never] at he
    obtain ⟨he1, he2⟩ := he
    cases hx : x.run arr q with
    | ok r =>
      obtain ⟨a, p'⟩ := r
      cases hy : y.run arr p' with
      | ok s =>
        obtain ⟨b, p''⟩ := s
        exact ⟨f a b, p'', by simp only [hy]⟩
      | error k =>
        obtain ⟨b, q'', hb⟩ := y.swit he2 arr p'
        rw [hb] at hy; exact absurd hy (by simp)
    | error k =>
      obtain ⟨a, q', ha⟩ := x.swit he1 arr q
      rw [ha] at hx; exact absurd hx (by simp)

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

/-- Parse a decimal natural number (one or more digits). Always consumes on success.
On failure the furthest offset is the current position. -/
@[inline] def GParser.nat : GParser conditional Nat where
  run := fun arr p0 =>
    if h : p0 < arr.size then
      let b := arr[p0]; if 48 ≤ b && b ≤ 57 then .ok (natFwd arr 0 p0) else .error p0
    else .error p0
  cwit := by
    intro arr q a q' heq
    split at heq
    · rename_i hbound
      by_cases hd : (48 ≤ arr[q] && arr[q] ≤ 57) = true
      · have hgt := natFwd_gt arr 0 q hbound hd
        simp only [hd, if_true, Except.ok.injEq] at heq
        rw [heq] at hgt
        exact hgt
      · simp only [Bool.not_eq_true] at hd
        simp [hd] at heq
    · exact absurd heq (by simp)
  ewit := by intro he; exact absurd he (by decide)
  swit := by intro he; exact absurd he (by decide)

/-- Consume exactly `n` bytes if available.
On failure the furthest offset is the current position. -/
@[inline] def GParser.takeN (n : Nat) : GParser fallible Unit where
  run := fun arr p => if p + n ≤ arr.size then .ok ((), p + n) else .error p
  cwit := by
    intro arr q a q' heq
    split at heq
    · simp only [Except.ok.injEq, Prod.mk.injEq] at heq; omega
    · exact absurd heq (by simp)
  ewit := by intro he; exact absurd he (by decide)
  swit := by intro he; exact absurd he (by decide)

/-- Zero-or-more `p` (always-consuming) into a list. Total (via `foldFwd`).
Always succeeds (result is `.ok`). -/
@[inline] def GParser.many (p : GParser ⟨ge, always⟩ α) : GParser flexible (List α) where
  run := fun arr pos =>
    match foldFwd (fun acc x => x :: acc) p arr [] pos with
    | (xs, q) => .ok (xs.reverse, q)
  cwit := by
    intro arr pos b q' heq
    have hge := foldFwd_ge (fun acc x => x :: acc) p arr ([] : List α) pos
    split at heq
    next xs q hfold =>
      simp only [Except.ok.injEq, Prod.mk.injEq] at heq
      obtain ⟨_, rfl⟩ := heq
      rw [hfold] at hge
      exact hge
  ewit := by intro he; exact absurd he (by decide)
  swit := by
    intro _ arr pos
    split
    next xs q _ => exact ⟨xs.reverse, q, rfl⟩

/-- Parse a `ByteArray` from offset 0, returning only the value (no position).
Maps `.ok (a, _)` to `some a` and `.error _` to `none` so existing callers are
unchanged. -/
@[inline] def GParser.parse (p : GParser g α) (arr : ByteArray) : Option α :=
  match p.run arr 0 with
  | .ok (a, _) => some a
  | .error _   => none

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
