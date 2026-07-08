/-
Copyright 2026 Jonathan Cubides. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Grip.Grade
import Grip.Error

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
  or `.error e` on failure where `e.pos` is the furthest byte offset reached and
  `e.expected` is the set of labels expected there. -/
  run : ByteArray → Nat → Except Err (α × Nat)
  /-- Consumption soundness: a successful parse advances the offset exactly as the
  grade's `consumes` component claims (`always ⇒ q<q'`, `possibly ⇒ q≤q'`,
  `never ⇒ q=q'`). -/
  cwit : ∀ {arr q a q'}, run arr q = .ok (a, q') → consumptionWitness q q' g.consumes
  /-- Error soundness, must-fail direction: a grade claiming `always`-error never
  succeeds — for every input there exists a furthest failure `e`. -/
  ewit : g.errors = always → ∀ arr q, ∃ e : Err, run arr q = .error e
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
  obtain ⟨e, he'⟩ := p.ewit he arr q
  rw [he'] at h; exact absurd h (by simp)

/-- A failure rules out the `never`-error grade (via `swit`). -/
theorem GParser.errors_ne_never {g : Grade} {α} (p : GParser g α) {arr q e}
    (h : p.run arr q = .error e) : g.errors ≠ never := fun he => by
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
  run := fun _ p => .error ⟨p, []⟩
  cwit := by intro arr q a q' h; exact absurd h (by simp)
  ewit := by intro _ arr q; exact ⟨⟨q, []⟩, rfl⟩
  swit := by intro he; exact absurd he (by decide)

/-- Consume one byte satisfying `f`, or fail without consuming.
On failure the furthest offset is the current position `p`. -/
@[inline] def GParser.satisfy (f : UInt8 → Bool) : GParser conditional UInt8 where
  run := fun arr p =>
    if h : p < arr.size then
      (if f arr[p] then .ok (arr[p], p + 1) else .error ⟨p, []⟩)
    else .error ⟨p, []⟩
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
      (if arr[p] == c then .ok ((), p + 1) else .error ⟨p, []⟩)
    else .error ⟨p, []⟩
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
    | .error e    => .error e
  cwit := by
    intro arr q b q' heq
    split at heq
    next a p' hx =>
      simp only [Except.ok.injEq, Prod.mk.injEq] at heq
      obtain ⟨_, rfl⟩ := heq
      exact x.cwit hx
    next e hx => exact absurd heq (by simp)
  ewit := by
    intro he arr q
    obtain ⟨e, he'⟩ := x.ewit he arr q
    exact ⟨e, by simp only [he']⟩
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
    | .error e    => .error e
  cwit := by
    intro arr q a q' heq
    split at heq
    next fst p' hx =>
      simpa only [grade_mul_consumes] using cw_seq (x.cwit hx) (y.cwit heq)
    next e hx => exact absurd heq (by simp)
  ewit := by
    intro he arr q
    simp only [grade_mul_errors, Necessity.max_always] at he
    rcases he with he | he
    · obtain ⟨e, he'⟩ := x.ewit he arr q
      exact ⟨e, by simp only [he']⟩
    · cases hx : x.run arr q with
      | ok r =>
        obtain ⟨_, p'⟩ := r
        obtain ⟨e, he'⟩ := y.ewit he arr p'
        exact ⟨e, he'⟩
      | error e => exact ⟨e, rfl⟩
  swit := by
    intro he arr q
    simp only [grade_mul_errors, Necessity.max_never] at he
    obtain ⟨he1, he2⟩ := he
    cases hx : x.run arr q with
    | ok r =>
      obtain ⟨c, p'⟩ := r
      obtain ⟨a, q', ha⟩ := y.swit he2 arr p'
      exact ⟨a, q', ha⟩
    | error e =>
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
      | .error e     => .error e
    | .error e => .error e
  cwit := by
    intro arr q a q' heq
    split at heq
    next fst p' hx =>
      split at heq
      next snd p'' hy =>
        simp only [Except.ok.injEq, Prod.mk.injEq] at heq
        obtain ⟨_, rfl⟩ := heq
        simpa only [grade_mul_consumes] using cw_seq (x.cwit hx) (y.cwit hy)
      next e hy => exact absurd heq (by simp)
    next e hx => exact absurd heq (by simp)
  ewit := by
    intro he arr q
    simp only [grade_mul_errors, Necessity.max_always] at he
    rcases he with he | he
    · obtain ⟨e, he'⟩ := x.ewit he arr q
      exact ⟨e, by simp only [he']⟩
    · cases hx : x.run arr q with
      | ok r =>
        obtain ⟨_, p'⟩ := r
        obtain ⟨e, he'⟩ := y.ewit he arr p'
        exact ⟨e, by simp only [he']⟩
      | error e => exact ⟨e, rfl⟩
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
      | error e =>
        obtain ⟨b, q'', hb⟩ := y.swit he2 arr p'
        rw [hb] at hy; exact absurd hy (by simp)
    | error e =>
      obtain ⟨a, q', ha⟩ := x.swit he1 arr q
      rw [ha] at hx; exact absurd hx (by simp)

/-- Ordered choice; grade follows `Grade.choice`.
On failure, the two errors are merged furthest-wins: if one branch reached a
farther offset, that error wins; on a tie the expected-label sets are unioned.
This is the megaparsec-style furthest-failure merge. -/
@[inline] def GParser.alt (x : GParser ⟨ge, gc⟩ α) (y : GParser ⟨ge', gc'⟩ α) :
    GParser ⟨min ge ge', ge.ite gc' gc⟩ α where
  run := fun arr p =>
    match x.run arr p with
    | .ok r  => .ok r
    | .error ex =>
      match y.run arr p with
      | .ok r  => .ok r
      | .error ey =>
        if ex.pos < ey.pos then .error ey
        else if ey.pos < ex.pos then .error ex
        else .error ⟨ex.pos, ex.expected ++ ey.expected⟩
  cwit := by
    intro arr q a q' heq
    split at heq
    · -- x succeeded
      rename_i r hx
      obtain rfl : r = (a, q') := Except.ok.inj heq
      exact consumptionWitness.ite_left
        (le_possibly_of_ne_always (x.errors_ne_always hx)) (x.cwit hx)
    · -- x failed; try y
      rename_i ex hx
      split at heq
      · rename_i r hy
        obtain rfl : r = (a, q') := Except.ok.inj heq
        exact consumptionWitness.ite_right
          (possibly_le_of_ne_never (x.errors_ne_never hx)) (y.cwit hy)
      · -- Both branches failed; heq is an if-then-else of .error cases.
        -- All branches yield .error, so heq : .error ... = .ok ... is absurd.
        rename_i ey _hy
        by_cases h1 : ex.pos < ey.pos
        · rw [if_pos h1] at heq; exact absurd heq (by simp)
        · by_cases h2 : ey.pos < ex.pos
          · rw [if_neg h1, if_pos h2] at heq; exact absurd heq (by simp)
          · rw [if_neg h1, if_neg h2] at heq; exact absurd heq (by simp)
  ewit := by
    intro he arr q
    simp only [Necessity.min_always] at he
    obtain ⟨he1, he2⟩ := he
    obtain ⟨ex, hex⟩ := x.ewit he1 arr q
    obtain ⟨ey, hey⟩ := y.ewit he2 arr q
    by_cases h1 : ex.pos < ey.pos
    · exact ⟨ey, by simp only [hex, hey, if_pos h1]⟩
    · by_cases h2 : ey.pos < ex.pos
      · exact ⟨ex, by simp only [hex, hey, if_neg h1, if_pos h2]⟩
      · exact ⟨⟨ex.pos, ex.expected ++ ey.expected⟩,
               by simp only [hex, hey, if_neg h1, if_neg h2]⟩
  swit := by
    intro he arr q
    simp only [Necessity.min_never] at he
    cases hx : x.run arr q with
    | ok r =>
      obtain ⟨a, q'⟩ := r
      exact ⟨a, q', rfl⟩
    | error ex =>
      cases hy : y.run arr q with
      | ok r =>
        obtain ⟨a, q'⟩ := r
        exact ⟨a, q', rfl⟩
      | error ey =>
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
      if f arr[p] then (GParser.takeWhile f).run arr p else .error ⟨p, []⟩
    else .error ⟨p, []⟩
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
    | .error e    => .error e
  cwit := by
    intro arr q a q' heq
    split at heq
    next fst p' hx =>
      simpa only [grade_mul_consumes] using cw_seq (x.cwit hx) ((f fst).cwit heq)
    next e hx => exact absurd heq (by simp)
  ewit := by
    intro he arr q
    simp only [grade_mul_errors, Necessity.max_always] at he
    rcases he with he | he
    · obtain ⟨e, he'⟩ := x.ewit he arr q
      exact ⟨e, by simp only [he']⟩
    · cases hx : x.run arr q with
      | ok r =>
        obtain ⟨fst, p'⟩ := r
        obtain ⟨e, he'⟩ := (f fst).ewit he arr p'
        exact ⟨e, he'⟩
      | error e => exact ⟨e, rfl⟩
  swit := by
    intro he arr q
    simp only [grade_mul_errors, Necessity.max_never] at he
    obtain ⟨he1, he2⟩ := he
    cases hx : x.run arr q with
    | ok r =>
      obtain ⟨fst, p'⟩ := r
      obtain ⟨a, q', ha⟩ := (f fst).swit he2 arr p'
      exact ⟨a, q', ha⟩
    | error e =>
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
      | .error e     => .error e
    | .error e => .error e
  cwit := by
    intro arr q a q' heq
    split at heq
    next fst p' hx =>
      split at heq
      next snd p'' hy =>
        simp only [Except.ok.injEq, Prod.mk.injEq] at heq
        obtain ⟨_, rfl⟩ := heq
        simpa only [grade_mul_consumes] using cw_seq (x.cwit hx) (y.cwit hy)
      next e hy => exact absurd heq (by simp)
    next e hx => exact absurd heq (by simp)
  ewit := by
    intro he arr q
    simp only [grade_mul_errors, Necessity.max_always] at he
    rcases he with he | he
    · obtain ⟨e, he'⟩ := x.ewit he arr q
      exact ⟨e, by simp only [he']⟩
    · cases hx : x.run arr q with
      | ok r =>
        obtain ⟨_, p'⟩ := r
        obtain ⟨e, he'⟩ := y.ewit he arr p'
        exact ⟨e, by simp only [he']⟩
      | error e => exact ⟨e, rfl⟩
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
      | error e =>
        obtain ⟨b, q'', hb⟩ := y.swit he2 arr p'
        rw [hb] at hy; exact absurd hy (by simp)
    | error e =>
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
      let b := arr[p0]; if 48 ≤ b && b ≤ 57 then .ok (natFwd arr 0 p0) else .error ⟨p0, []⟩
    else .error ⟨p0, []⟩
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
  run := fun arr p => if p + n ≤ arr.size then .ok ((), p + n) else .error ⟨p, []⟩
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

/-- Run a parser from offset 0, returning `some value` on success and `none` on
failure.  The error payload is discarded; use `GParser.parse` (in `Grip.Parser`)
for a positioned `ParseError`. -/
@[inline] def GParser.run? (p : GParser g α) (arr : ByteArray) : Option α :=
  match p.run arr 0 with
  | .ok (a, _) => some a
  | .error _   => none

/-- Replace the expected-label set of `p`'s failure with `[name]`.
Mirrors megaparsec's `<?>` operator: on success the result is unchanged; on
failure the `expected` field is overwritten so error messages read
"expected name" rather than a raw position. -/
@[inline] def GParser.label (name : String) (p : GParser g α) : GParser g α where
  run arr q := match p.run arr q with
    | .ok r  => .ok r
    | .error e => .error { e with expected := [name] }
  cwit := by
    intro arr q a q' h
    split at h
    · rename_i r hp
      exact p.cwit (Except.ok.inj h ▸ hp)
    · exact absurd h (by simp)
  ewit := by
    intro he arr q
    obtain ⟨e, he'⟩ := p.ewit he arr q
    exact ⟨{ e with expected := [name] }, by simp [he']⟩
  swit := by
    intro he arr q
    obtain ⟨a, q', ha⟩ := p.swit he arr q
    exact ⟨a, q', by simp [ha]⟩

/-- Attach an expected label to a parser (megaparsec-style `<?>`).
`p <?> "name"` produces "expected name" on failure at the same position. -/
infixl:10 " <?> " => fun p name => GParser.label name p

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

/-- Default `GParser conditional α`: always fails at the current offset.
Satisfies Lean's `[Inhabited]` requirement for `partial def` recursion over
`GParser conditional α` return types (grip has no `fix` combinator yet). -/
instance : Inhabited (GParser conditional α) :=
  ⟨{ run := fun _ p => .error ⟨p, []⟩,
     cwit := by intro arr q a q' h; exact absurd h (by simp),
     ewit := by intro he; exact absurd he (by decide),
     swit := by intro he; exact absurd he (by decide) }⟩

/-! ### Recursion via a fixpoint

`GParser.fix` ties the knot on a parser transformer, giving the body a reference back
to the whole parser so recursive grammars can be written from combinators. The
self-reference is `conditional` (always-consuming), so a well-behaved grammar shrinks
the input before each recursive call.

It is implemented with `partial def`: grip's byte core is not size-indexed, so an
efficient kernel-total `fix` is impractical. A runtime clamp downgrades a
non-advancing success to a failure, which keeps the `always`-consume grade SOUND even
though termination is not kernel-checked. A left-recursive body (one that reaches its
recursive call without consuming) therefore fails rather than looping. This is the
honest totality-not-productivity limitation, not a defect. -/

/-- Clamp a raw result so a success that did not advance past `q` becomes a failure at
`q`. This is what makes the `conditional` (`always`-consume) witness hold for `fix`
without unfolding the `partial` recursion. -/
@[inline] private def clampAdvance (q : Nat) : Except Err (α × Nat) → Except Err (α × Nat)
  | .ok (x, q') => if q < q' then .ok (x, q') else .error ⟨q, []⟩
  | .error e    => .error e

/-- The recursive run: applies `f` to a `self` whose recursive calls are clamped. -/
partial def GParser.fixRun (f : GParser conditional α → GParser conditional α)
    (arr : ByteArray) (q : Nat) : Except Err (α × Nat) :=
  let self : GParser conditional α :=
    { run := fun a p => clampAdvance p (GParser.fixRun f a p)
      cwit := by
        intro a p x p' h
        show p < p'
        simp only [clampAdvance] at h
        split at h
        · split at h
          · rename_i hlt
            simp only [Except.ok.injEq, Prod.mk.injEq] at h
            omega
          · exact absurd h (by simp)
        · exact absurd h (by simp)
      ewit := by intro he; exact absurd he (by decide)
      swit := by intro he; exact absurd he (by decide) }
  (f self).run arr q

/-- Build a recursive `conditional` parser as the fixpoint of `f`. See the module note
above for the totality-not-productivity caveat. -/
@[specialize] def GParser.fix (f : GParser conditional α → GParser conditional α) :
    GParser conditional α where
  run arr q := clampAdvance q (GParser.fixRun f arr q)
  cwit := by
    intro arr q a q' h
    show q < q'
    simp only [clampAdvance] at h
    split at h
    · split at h
      · rename_i hlt
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        omega
      · exact absurd h (by simp)
    · exact absurd h (by simp)
  ewit := by intro he; exact absurd he (by decide)
  swit := by intro he; exact absurd he (by decide)

end Grip

/-! ### Sanity: the graded byte backend parses. -/
section
open Grip

private def digits : GParser conditional Nat :=
  GParser.takeWhile1 (fun b => 48 ≤ b && b ≤ 57)

private def sample :=
  GParser.seqR (GParser.byte 40) (GParser.seqL digits (GParser.byte 41))  -- "(" digits ")"

#guard (GParser.run? digits "123".toUTF8) == some 3        -- 3 digit bytes consumed
#guard (GParser.run? sample "(42)".toUTF8) == some 2       -- 2 digit bytes inside parens
#guard (GParser.run? sample "(42".toUTF8) == none          -- missing ')'
#guard (GParser.run? (GParser.foldMany (· + ·) 0 digits) "".toUTF8) == some 0

-- fix: a recursive nested-parens parser returning the nesting depth. Each level
-- consumes "(" before recursing, so the always-consume clamp never fires on
-- balanced input; unbalanced input fails.
private def parenDepth : GParser conditional Nat :=
  GParser.fix fun self =>
    GParser.map (· + 1)
      (GParser.seqR (GParser.byte 40)
        (GParser.seqL (GParser.alt self (GParser.pure 0)) (GParser.byte 41)))

#guard (GParser.run? parenDepth "()".toUTF8) == some 1
#guard (GParser.run? parenDepth "((()))".toUTF8) == some 3
#guard (GParser.run? parenDepth "(()".toUTF8) == none            -- unbalanced

-- BEq for Except Err, needed by the #guard comparisons below.
private instance instBEqExceptErr {β : Type} [BEq β] : BEq (Except Err β) where
  beq
    | .error e1, .error e2 => e1 == e2
    | .ok a,     .ok b     => a == b
    | _,         _         => false

-- Error payload: bare failure records pos; label sets expected.
#guard (digits.run "abc".toUTF8 0 == (.error ⟨0, []⟩ : Except Err (Nat × Nat)))
#guard ((digits <?> "digit").run "abc".toUTF8 0
        == (.error ⟨0, ["digit"]⟩ : Except Err (Nat × Nat)))
-- Tie-merge: both branches fail at pos 0; expected sets are unioned.
private def byteA : GParser conditional Unit := GParser.byte 65
private def byteB : GParser conditional Unit := GParser.byte 66
#guard ((GParser.alt (byteA <?> "A") (byteB <?> "B")).run "c".toUTF8 0
        == (.error ⟨0, ["A", "B"]⟩ : Except Err (Unit × Nat)))

end
