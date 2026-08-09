/-
Copyright (c) 2026 Jonathan Cubides. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Prieto-Cubides
-/

import Grip.Graded

/-!
# Grip.Byte: point combinators over the graded byte backend

The non-looping combinators. Atomic byte readers (`satisfy`, `byte`, `takeN`), the
functor / sequence / choice / monad algebra (`map`, `seqR`, `seqL`, `alt`, `bind`,
`map2`), the `capture`/`captureWith`/`captureWith?` slice readers, first-byte
`dispatch`, and the `<?>` label. The total scanning loops are in `Grip.Scan`; the
graded type, weakening, `run?`, and `fix` are in `Grip.Graded`.
-/

open Modality
open Grade

namespace Grip

variable {g g' : Grade} {ge ge' gc gc' : Modality} {α β : Type}

/-- Consume nothing, never fail. -/
@[inline] def GParser.pure (a : α) : GParser 1 α where
  run := fun _ p => .ok a p
  cwit := by
    intro arr q b q' h
    simp only [ParseResult.ok.injEq] at h
    exact h.2
  ewit := by intro he; exact absurd he (by decide)
  swit := by intro _ arr q; exact ⟨a, q, rfl⟩
  bwit := by intro arr q b q' hq h; simp only [ParseResult.ok.injEq] at h; omega
  fwit := by intro arr q e hq h; exact absurd h (by simp)

/-- Always fail, recording the current position as the furthest offset reached. -/
@[inline] def GParser.fail : GParser empty α where
  run := fun _ p => .error ⟨p, []⟩
  cwit := by intro arr q a q' h; exact absurd h (by simp)
  ewit := by intro _ arr q; exact ⟨⟨q, []⟩, rfl⟩
  swit := by intro he; exact absurd he (by decide)
  bwit := by intro arr q a q' hq h; exact absurd h (by simp)
  fwit := by
    intro arr q e hq h
    simp only [ParseResult.error.injEq] at h
    subst e
    exact ⟨Nat.le_refl q, hq⟩

/-- Consume one byte satisfying `f`, or fail without consuming.
On failure the furthest offset is the current position `p`. -/
@[inline] def GParser.satisfy (f : UInt8 → Bool) : GParser conditional UInt8 where
  run := fun arr p =>
    if h : p < arr.size then
      (if f arr[p] then .ok arr[p] (p + 1) else .error ⟨p, []⟩)
    else .error ⟨p, []⟩
  cwit := by
    intro arr q a q' heq
    split at heq
    · split at heq
      · simp only [ParseResult.ok.injEq] at heq; omega
      · exact absurd heq (by simp)
    · exact absurd heq (by simp)
  ewit := by intro he; exact absurd he (by decide)
  swit := by intro he; exact absurd he (by decide)
  bwit := by
    intro arr q a q' hq heq
    split at heq
    · split at heq
      · simp only [ParseResult.ok.injEq] at heq; omega
      · exact absurd heq (by simp)
    · exact absurd heq (by simp)
  fwit := by
    intro arr q e hq heq
    split at heq
    · split at heq
      · contradiction
      · simp only [ParseResult.error.injEq] at heq
        subst e
        exact ⟨Nat.le_refl q, hq⟩
    · simp only [ParseResult.error.injEq] at heq
      subst e
      exact ⟨Nat.le_refl q, hq⟩

/-- Match a specific byte.
On failure the furthest offset is the current position `p`. -/
@[inline] def GParser.byte (c : UInt8) : GParser conditional Unit where
  run := fun arr p =>
    if h : p < arr.size then
      (if arr[p] == c then .ok () (p + 1) else .error ⟨p, []⟩)
    else .error ⟨p, []⟩
  cwit := by
    intro arr q a q' heq
    split at heq
    · split at heq
      · simp only [ParseResult.ok.injEq] at heq; omega
      · exact absurd heq (by simp)
    · exact absurd heq (by simp)
  ewit := by intro he; exact absurd he (by decide)
  swit := by intro he; exact absurd he (by decide)
  bwit := by
    intro arr q a q' hq heq
    split at heq
    · split at heq
      · simp only [ParseResult.ok.injEq] at heq; omega
      · exact absurd heq (by simp)
    · exact absurd heq (by simp)
  fwit := by
    intro arr q e hq heq
    split at heq
    · split at heq
      · contradiction
      · simp only [ParseResult.error.injEq] at heq
        subst e
        exact ⟨Nat.le_refl q, hq⟩
    · simp only [ParseResult.error.injEq] at heq
      subst e
      exact ⟨Nat.le_refl q, hq⟩

/-- Return the input slice a parser consumed, decoded as text (grade preserved). Lets
combinator parsers build real syntax trees (atom names, identifiers, header fields)
instead of only structural counts. Invalid UTF-8 in the slice decodes to `""`. -/
@[inline] def GParser.capture (p : GParser g α) : GParser g String where
  run := fun arr q =>
    match p.run arr q with
    | .ok _ q' => .ok ((String.fromUTF8? (arr.extract q q')).getD "") q'
    | .error e => .error e
  cwit := by
    intro arr q b q' heq
    split at heq
    next a p' hx =>
      simp only [ParseResult.ok.injEq] at heq
      obtain ⟨_, rfl⟩ := heq
      exact p.cwit hx
    next e hx => exact absurd heq (by simp)
  ewit := by
    intro he arr q
    obtain ⟨e, he'⟩ := p.ewit he arr q
    exact ⟨e, by simp only [he']⟩
  swit := by
    intro he arr q
    obtain ⟨a, q', ha⟩ := p.swit he arr q
    exact ⟨(String.fromUTF8? (arr.extract q q')).getD "", q', by simp only [ha]⟩
  bwit := by
    intro arr q b q' hq heq
    split at heq
    next a p' hx =>
      simp only [ParseResult.ok.injEq] at heq
      obtain ⟨_, rfl⟩ := heq
      exact p.bwit hq hx
    next e hx => exact absurd heq (by simp)
  fwit := by
    intro arr q e hq heq
    split at heq
    next a q' hp => contradiction
    next e' hp =>
      simp only [ParseResult.error.injEq] at heq
      subst e
      exact p.fwit hq hp

/-- Like `capture`, but hand the consumed byte range `(arr, start, stop)` to `f` instead
of decoding it to a `String`. Lets a value parser fold over the raw input bytes directly,
with no `extract`/`fromUTF8?`/`String` round-trip. -/
@[inline] def GParser.captureWith (f : ByteArray → Nat → Nat → β) (p : GParser g α) :
    GParser g β where
  run := fun arr q =>
    match p.run arr q with
    | .ok _ q' => .ok (f arr q q') q'
    | .error e => .error e
  cwit := by
    intro arr q b q' heq
    split at heq
    next a p' hx =>
      simp only [ParseResult.ok.injEq] at heq
      obtain ⟨_, rfl⟩ := heq
      exact p.cwit hx
    next e hx => exact absurd heq (by simp)
  ewit := by
    intro he arr q
    obtain ⟨e, he'⟩ := p.ewit he arr q
    exact ⟨e, by simp only [he']⟩
  swit := by
    intro he arr q
    obtain ⟨a, q', ha⟩ := p.swit he arr q
    exact ⟨f arr q q', q', by simp only [ha]⟩
  bwit := by
    intro arr q b q' hq heq
    split at heq
    next a p' hx =>
      simp only [ParseResult.ok.injEq] at heq
      obtain ⟨_, rfl⟩ := heq
      exact p.bwit hq hx
    next e hx => exact absurd heq (by simp)
  fwit := by
    intro arr q e hq heq
    split at heq
    next a q' hp => contradiction
    next e' hp =>
      simp only [ParseResult.error.injEq] at heq
      subst e
      exact p.fwit hq hp

/-- Like `captureWith`, but `f` may reject the consumed range by returning `none`, in which
case the parse fails at the entry offset. The result grade keeps `p`'s consumption but sets
`errors := possibly` (the extra failure path), so a `conditional` `p` yields a `conditional`
parser. Lets a value decoder veto a syntactically-valid but semantically-out-of-range slice
(e.g. a JSON exponent so large that folding it would blow up). -/
@[inline] def GParser.captureWith? (f : ByteArray → Nat → Nat → Option β) (p : GParser g α) :
    GParser ⟨possibly, g.consumes⟩ β where
  run := fun arr q =>
    match p.run arr q with
    | .ok _ q' => match f arr q q' with
      | some b => .ok b q'
      | none   => .error ⟨q, []⟩
    | .error e => .error e
  cwit := by
    intro arr q b q' heq
    split at heq
    next a p' hx =>
      split at heq
      next b0 hf =>
        simp only [ParseResult.ok.injEq] at heq
        obtain ⟨_, rfl⟩ := heq
        exact p.cwit hx
      next hf => exact absurd heq (by simp)
    next e hx => exact absurd heq (by simp)
  ewit := by intro he; exact Modality.noConfusion he
  swit := by intro he; exact Modality.noConfusion he
  bwit := by
    intro arr q b q' hq heq
    split at heq
    next a p' hx =>
      split at heq
      next b0 hf =>
        simp only [ParseResult.ok.injEq] at heq
        obtain ⟨_, rfl⟩ := heq
        exact p.bwit hq hx
      next hf => exact absurd heq (by simp)
    next e hx => exact absurd heq (by simp)
  fwit := by
    intro arr q e hq heq
    split at heq
    next a q' hp =>
      split at heq
      next b hf => contradiction
      next hf =>
        simp only [ParseResult.error.injEq] at heq
        subst e
        exact ⟨Nat.le_refl q, hq⟩
    next e' hp =>
      simp only [ParseResult.error.injEq] at heq
      subst e
      exact p.fwit hq hp

/-- First-byte dispatch: read the current byte and run the parser `select` chooses for
it, without an intermediate allocation. Fails without consuming at end-of-input. This is
`peek`-then-branch fused into one step, so a keyword/number/string/array/object choice
costs a single byte read and a jump rather than an `alt` chain of failed attempts. -/
@[inline] def GParser.dispatch (select : UInt8 → GParser conditional α) :
    GParser conditional α where
  run := fun arr p => if h : p < arr.size then (select arr[p]).run arr p else .error ⟨p, []⟩
  cwit := by
    intro arr q a q' heq
    split at heq
    · exact (select _).cwit heq
    · exact absurd heq (by simp)
  ewit := by intro he; exact absurd he (by decide)
  swit := by intro he; exact absurd he (by decide)
  bwit := by
    intro arr q a q' hq heq
    split at heq
    · exact (select _).bwit hq heq
    · exact absurd heq (by simp)
  fwit := by
    intro arr q e hq heq
    split at heq
    · exact (select _).fwit hq heq
    · simp only [ParseResult.error.injEq] at heq
      subst e
      exact ⟨Nat.le_refl q, hq⟩

/-- Map over the result (grade preserved). -/
@[inline] def GParser.map (h : α → β) (x : GParser g α) : GParser g β where
  run := fun arr p =>
    match x.run arr p with
    | .ok a p' => .ok (h a) p'
    | .error e => .error e
  cwit := by
    intro arr q b q' heq
    split at heq
    next a p' hx =>
      simp only [ParseResult.ok.injEq] at heq
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
  bwit := by
    intro arr q b q' hq heq
    split at heq
    next a p' hx =>
      simp only [ParseResult.ok.injEq] at heq
      obtain ⟨_, rfl⟩ := heq
      exact x.bwit hq hx
    next e hx => exact absurd heq (by simp)
  fwit := by
    intro arr q e hq heq
    split at heq
    next a q' hx => contradiction
    next e' hx =>
      simp only [ParseResult.error.injEq] at heq
      subst e
      exact x.fwit hq hx

/-- Sequence, keeping the right value; grades multiply.
Furthest offset from either `x` or `y` propagates on failure. -/
@[inline] def GParser.seqR (x : GParser g α) (y : GParser g' β) : GParser (g * g') β where
  run := fun arr p =>
    match x.run arr p with
    | .ok _ p' => y.run arr p'
    | .error e => .error e
  cwit := by
    intro arr q a q' heq
    split at heq
    next fst p' hx =>
      simpa only [grade_mul_consumes] using cw_seq (x.cwit hx) (y.cwit heq)
    next e hx => exact absurd heq (by simp)
  ewit := by
    intro he arr q
    simp only [grade_mul_errors, Modality.max_always] at he
    rcases he with he | he
    · obtain ⟨e, he'⟩ := x.ewit he arr q
      exact ⟨e, by simp only [he']⟩
    · cases hx : x.run arr q with
      | ok fst p' =>
        obtain ⟨e, he'⟩ := y.ewit he arr p'
        exact ⟨e, he'⟩
      | error e => exact ⟨e, rfl⟩
  swit := by
    intro he arr q
    simp only [grade_mul_errors, Modality.max_never] at he
    obtain ⟨he1, he2⟩ := he
    cases hx : x.run arr q with
    | ok c p' =>
      obtain ⟨a, q', ha⟩ := y.swit he2 arr p'
      exact ⟨a, q', ha⟩
    | error e =>
      obtain ⟨a, q', ha⟩ := x.swit he1 arr q
      rw [ha] at hx; exact absurd hx (by simp)
  bwit := by
    intro arr q a q' hq heq
    split at heq
    next fst p' hx => exact y.bwit (x.bwit hq hx) heq
    next e hx => exact absurd heq (by simp)
  fwit := by
    intro arr q e hq heq
    split at heq
    next fst q' hx =>
      have hy := y.fwit (x.bwit hq hx) heq
      exact ⟨Nat.le_trans (consumptionWitness.le (x.cwit hx)) hy.1, hy.2⟩
    next e' hx =>
      simp only [ParseResult.error.injEq] at heq
      subst e
      exact x.fwit hq hx

/-- Sequence, keeping the left value; grades multiply.
Furthest offset propagates on failure. -/
@[inline] def GParser.seqL (x : GParser g α) (y : GParser g' β) : GParser (g * g') α where
  run := fun arr p =>
    match x.run arr p with
    | .ok a p' =>
      match y.run arr p' with
      | .ok _ p'' => .ok a p''
      | .error e  => .error e
    | .error e => .error e
  cwit := by
    intro arr q a q' heq
    split at heq
    next fst p' hx =>
      split at heq
      next snd p'' hy =>
        simp only [ParseResult.ok.injEq] at heq
        obtain ⟨_, rfl⟩ := heq
        simpa only [grade_mul_consumes] using cw_seq (x.cwit hx) (y.cwit hy)
      next e hy => exact absurd heq (by simp)
    next e hx => exact absurd heq (by simp)
  ewit := by
    intro he arr q
    simp only [grade_mul_errors, Modality.max_always] at he
    rcases he with he | he
    · obtain ⟨e, he'⟩ := x.ewit he arr q
      exact ⟨e, by simp only [he']⟩
    · cases hx : x.run arr q with
      | ok fst p' =>
        obtain ⟨e, he'⟩ := y.ewit he arr p'
        exact ⟨e, by simp only [he']⟩
      | error e => exact ⟨e, rfl⟩
  swit := by
    intro he arr q
    simp only [grade_mul_errors, Modality.max_never] at he
    obtain ⟨he1, he2⟩ := he
    cases hx : x.run arr q with
    | ok a p' =>
      cases hy : y.run arr p' with
      | ok _ p'' =>
        exact ⟨a, p'', by simp only [hy]⟩
      | error e =>
        obtain ⟨b, q'', hb⟩ := y.swit he2 arr p'
        rw [hb] at hy; exact absurd hy (by simp)
    | error e =>
      obtain ⟨a, q', ha⟩ := x.swit he1 arr q
      rw [ha] at hx; exact absurd hx (by simp)
  bwit := by
    intro arr q a q' hq heq
    split at heq
    next fst p' hx =>
      split at heq
      next snd p'' hy =>
        simp only [ParseResult.ok.injEq] at heq
        obtain ⟨_, rfl⟩ := heq
        exact y.bwit (x.bwit hq hx) hy
      next e hy => exact absurd heq (by simp)
    next e hx => exact absurd heq (by simp)
  fwit := by
    intro arr q e hq heq
    split at heq
    next fst q' hx =>
      split at heq
      next snd q'' hy => contradiction
      next e' hy =>
        simp only [ParseResult.error.injEq] at heq
        subst e
        have hb := y.fwit (x.bwit hq hx) hy
        exact ⟨Nat.le_trans (consumptionWitness.le (x.cwit hx)) hb.1, hb.2⟩
    next e' hx =>
      simp only [ParseResult.error.injEq] at heq
      subst e
      exact x.fwit hq hx

/-- Ordered choice; grade follows `Grade.choice`.
On failure, the two errors are merged furthest-wins: if one branch reached a
farther offset, that error wins; on a tie the expected-label sets are unioned.
This is the megaparsec-style furthest-failure merge. -/
@[inline] def GParser.alt (x : GParser ⟨ge, gc⟩ α) (y : GParser ⟨ge', gc'⟩ α) :
    GParser ⟨min ge ge', ge.ite gc' gc⟩ α where
  run := fun arr p =>
    match x.run arr p with
    | .ok a p' => .ok a p'
    | .error ex =>
      match y.run arr p with
      | .ok a p' => .ok a p'
      | .error ey =>
        if ex.pos < ey.pos then .error ey
        else if ey.pos < ex.pos then .error ex
        else .error ⟨ex.pos, ex.expected ++ ey.expected⟩
  cwit := by
    intro arr q a q' heq
    split at heq
    · -- x succeeded
      rename_i b p' hx
      simp only [ParseResult.ok.injEq] at heq
      obtain ⟨rfl, rfl⟩ := heq
      exact consumptionWitness.ite_left
        (le_possibly_of_ne_always (x.errors_ne_always hx)) (x.cwit hx)
    · -- x failed; try y
      rename_i ex hx
      split at heq
      · rename_i b p' hy
        simp only [ParseResult.ok.injEq] at heq
        obtain ⟨rfl, rfl⟩ := heq
        exact consumptionWitness.ite_right
          (possibly_le_of_ne_never (x.errors_ne_never hx)) (y.cwit hy)
      · -- Both branches failed; heq is an if-then-else of .error cases.
        rename_i ey _hy
        by_cases h1 : ex.pos < ey.pos
        · rw [if_pos h1] at heq; exact absurd heq (by simp)
        · by_cases h2 : ey.pos < ex.pos
          · rw [if_neg h1, if_pos h2] at heq; exact absurd heq (by simp)
          · rw [if_neg h1, if_neg h2] at heq; exact absurd heq (by simp)
  ewit := by
    intro he arr q
    simp only [Modality.min_always] at he
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
    simp only [Modality.min_never] at he
    cases hx : x.run arr q with
    | ok a q' =>
      exact ⟨a, q', rfl⟩
    | error ex =>
      cases hy : y.run arr q with
      | ok a q' =>
        exact ⟨a, q', rfl⟩
      | error ey =>
        rcases he with hg | hg
        · obtain ⟨a, q', ha⟩ := x.swit hg arr q
          rw [ha] at hx; exact absurd hx (by simp)
        · obtain ⟨a, q', ha⟩ := y.swit hg arr q
          rw [ha] at hy; exact absurd hy (by simp)
  bwit := by
    intro arr q a q' hq heq
    split at heq
    · rename_i b p' hx
      simp only [ParseResult.ok.injEq] at heq
      obtain ⟨rfl, rfl⟩ := heq
      exact x.bwit hq hx
    · rename_i ex hx
      split at heq
      · rename_i b p' hy
        simp only [ParseResult.ok.injEq] at heq
        obtain ⟨rfl, rfl⟩ := heq
        exact y.bwit hq hy
      · rename_i ey _hy
        by_cases h1 : ex.pos < ey.pos
        · rw [if_pos h1] at heq; exact absurd heq (by simp)
        · by_cases h2 : ey.pos < ex.pos
          · rw [if_neg h1, if_pos h2] at heq; exact absurd heq (by simp)
          · rw [if_neg h1, if_neg h2] at heq; exact absurd heq (by simp)
  fwit := by
    intro arr q e hq heq
    split at heq
    · contradiction
    · rename_i ex hx
      split at heq
      · contradiction
      · rename_i ey hy
        have hbx := x.fwit hq hx
        have hby := y.fwit hq hy
        by_cases h1 : ex.pos < ey.pos
        · rw [if_pos h1] at heq
          simp only [ParseResult.error.injEq] at heq
          subst e
          exact hby
        · by_cases h2 : ey.pos < ex.pos
          · rw [if_neg h1, if_pos h2] at heq
            simp only [ParseResult.error.injEq] at heq
            subst e
            exact hbx
          · rw [if_neg h1, if_neg h2] at heq
            simp only [ParseResult.error.injEq] at heq
            subst e
            exact hbx

/-- Monadic bind; grades multiply.
Furthest offset propagates on failure. -/
@[inline] def GParser.bind (x : GParser g α) (f : α → GParser g' β) : GParser (g * g') β where
  run := fun arr p =>
    match x.run arr p with
    | .ok a p' => (f a).run arr p'
    | .error e => .error e
  cwit := by
    intro arr q a q' heq
    split at heq
    next fst p' hx =>
      simpa only [grade_mul_consumes] using cw_seq (x.cwit hx) ((f fst).cwit heq)
    next e hx => exact absurd heq (by simp)
  ewit := by
    intro he arr q
    simp only [grade_mul_errors, Modality.max_always] at he
    rcases he with he | he
    · obtain ⟨e, he'⟩ := x.ewit he arr q
      exact ⟨e, by simp only [he']⟩
    · cases hx : x.run arr q with
      | ok fst p' =>
        obtain ⟨e, he'⟩ := (f fst).ewit he arr p'
        exact ⟨e, he'⟩
      | error e => exact ⟨e, rfl⟩
  swit := by
    intro he arr q
    simp only [grade_mul_errors, Modality.max_never] at he
    obtain ⟨he1, he2⟩ := he
    cases hx : x.run arr q with
    | ok fst p' =>
      obtain ⟨a, q', ha⟩ := (f fst).swit he2 arr p'
      exact ⟨a, q', ha⟩
    | error e =>
      obtain ⟨a, q', ha⟩ := x.swit he1 arr q
      rw [ha] at hx; exact absurd hx (by simp)
  bwit := by
    intro arr q a q' hq heq
    split at heq
    next fst p' hx => exact (f fst).bwit (x.bwit hq hx) heq
    next e hx => exact absurd heq (by simp)
  fwit := by
    intro arr q e hq heq
    split at heq
    next fst q' hx =>
      have hf := (f fst).fwit (x.bwit hq hx) heq
      exact ⟨Nat.le_trans (consumptionWitness.le (x.cwit hx)) hf.1, hf.2⟩
    next e' hx =>
      simp only [ParseResult.error.injEq] at heq
      subst e
      exact x.fwit hq hx

/-- Apply a binary function across two parses; grades multiply.
Furthest offset propagates on failure. -/
@[inline] def GParser.map2 {γ : Type} (f : α → β → γ) (x : GParser g α) (y : GParser g' β) :
    GParser (g * g') γ where
  run := fun arr p =>
    match x.run arr p with
    | .ok a p' =>
      match y.run arr p' with
      | .ok b p'' => .ok (f a b) p''
      | .error e  => .error e
    | .error e => .error e
  cwit := by
    intro arr q a q' heq
    split at heq
    next fst p' hx =>
      split at heq
      next snd p'' hy =>
        simp only [ParseResult.ok.injEq] at heq
        obtain ⟨_, rfl⟩ := heq
        simpa only [grade_mul_consumes] using cw_seq (x.cwit hx) (y.cwit hy)
      next e hy => exact absurd heq (by simp)
    next e hx => exact absurd heq (by simp)
  ewit := by
    intro he arr q
    simp only [grade_mul_errors, Modality.max_always] at he
    rcases he with he | he
    · obtain ⟨e, he'⟩ := x.ewit he arr q
      exact ⟨e, by simp only [he']⟩
    · cases hx : x.run arr q with
      | ok fst p' =>
        obtain ⟨e, he'⟩ := y.ewit he arr p'
        exact ⟨e, by simp only [he']⟩
      | error e => exact ⟨e, rfl⟩
  swit := by
    intro he arr q
    simp only [grade_mul_errors, Modality.max_never] at he
    obtain ⟨he1, he2⟩ := he
    cases hx : x.run arr q with
    | ok a p' =>
      cases hy : y.run arr p' with
      | ok b p'' =>
        exact ⟨f a b, p'', by simp only [hy]⟩
      | error e =>
        obtain ⟨b, q'', hb⟩ := y.swit he2 arr p'
        rw [hb] at hy; exact absurd hy (by simp)
    | error e =>
      obtain ⟨a, q', ha⟩ := x.swit he1 arr q
      rw [ha] at hx; exact absurd hx (by simp)
  bwit := by
    intro arr q a q' hq heq
    split at heq
    next fst p' hx =>
      split at heq
      next snd p'' hy =>
        simp only [ParseResult.ok.injEq] at heq
        obtain ⟨_, rfl⟩ := heq
        exact y.bwit (x.bwit hq hx) hy
      next e hy => exact absurd heq (by simp)
    next e hx => exact absurd heq (by simp)
  fwit := by
    intro arr q e hq heq
    split at heq
    next fst q' hx =>
      split at heq
      next snd q'' hy => contradiction
      next e' hy =>
        simp only [ParseResult.error.injEq] at heq
        subst e
        have hb := y.fwit (x.bwit hq hx) hy
        exact ⟨Nat.le_trans (consumptionWitness.le (x.cwit hx)) hb.1, hb.2⟩
    next e' hx =>
      simp only [ParseResult.error.injEq] at heq
      subst e
      exact x.fwit hq hx

/-- Consume exactly `n` bytes if available.
On failure the furthest offset is the current position. -/
@[inline] def GParser.takeN (n : Nat) : GParser fallible Unit where
  run := fun arr p => if p + n ≤ arr.size then .ok () (p + n) else .error ⟨p, []⟩
  cwit := by
    intro arr q a q' heq
    split at heq
    · simp only [ParseResult.ok.injEq] at heq; omega
    · exact absurd heq (by simp)
  ewit := by intro he; exact absurd he (by decide)
  swit := by intro he; exact absurd he (by decide)
  bwit := by
    intro arr q a q' hq heq
    split at heq
    · simp only [ParseResult.ok.injEq] at heq; omega
    · exact absurd heq (by simp)
  fwit := by
    intro arr q e hq heq
    split at heq
    · contradiction
    · simp only [ParseResult.error.injEq] at heq
      subst e
      exact ⟨Nat.le_refl q, hq⟩

/-- Replace the expected-label set of `p`'s failure with `[name]`.
Mirrors megaparsec's `<?>` operator: on success the result is unchanged; on
failure the `expected` field is overwritten so error messages read
"expected name" rather than a raw position. -/
@[inline] def GParser.label (name : String) (p : GParser g α) : GParser g α where
  run arr q := match p.run arr q with
    | .ok a q' => .ok a q'
    | .error e => .error { e with expected := [name] }
  cwit := by
    intro arr q a q' h
    split at h
    · rename_i b p' hp
      simp only [ParseResult.ok.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact p.cwit hp
    · exact absurd h (by simp)
  ewit := by
    intro he arr q
    obtain ⟨e, he'⟩ := p.ewit he arr q
    exact ⟨{ e with expected := [name] }, by simp [he']⟩
  swit := by
    intro he arr q
    obtain ⟨a, q', ha⟩ := p.swit he arr q
    exact ⟨a, q', by simp [ha]⟩
  bwit := by
    intro arr q a q' hq h
    split at h
    · rename_i b p' hp
      simp only [ParseResult.ok.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact p.bwit hq hp
    · exact absurd h (by simp)
  fwit := by
    intro arr q e hq h
    split at h
    · contradiction
    · rename_i e' hp
      simp only [ParseResult.error.injEq] at h
      have hb : q ≤ e'.pos ∧ e'.pos ≤ arr.size := p.fwit hq hp
      simpa only [← h] using hb

/-- Attach an expected label to a parser (megaparsec-style `<?>`).
`p <?> "name"` produces "expected name" on failure at the same position. -/
infixl:10 " <?> " => fun p name => GParser.label name p

-- A `conditional` parser weakened to `fallible` typechecks (see `Grip.Graded`).
example (f : UInt8 → Bool) : GParser fallible UInt8 := GParser.weakenFallible (GParser.satisfy f)

end Grip
