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
@[inline]
def GParser.pure
    (a : α)
    : GParser 1 α
    where
  run := fun _ p => .ok a p
  cwit := by
    intro arr q b q' h
    simp only [ParseResult.ok.injEq] at h
    exact h.2
  ewit := nofun
  swit := by intro _ arr q; exact ⟨a, q, rfl⟩
  bwit := by intro arr q b q' hq h; simp only [ParseResult.ok.injEq] at h; omega
  fwit := fun _ h => nomatch h

/-- Always fail, recording the current position as the furthest offset reached. -/
@[inline]
def GParser.fail
    : GParser empty α
    where
  run := fun _ p => .error { pos := p }
  cwit := nofun
  ewit := by intro _ arr q; exact ⟨{ pos := q }, rfl⟩
  swit := nofun
  bwit := by intro arr q a q' hq h; nomatch h
  fwit := by
    intro arr q e hq h
    simp only [ParseResult.error.injEq] at h
    subst e
    exact ⟨Nat.le_refl q, hq⟩

/-- Whether the byte at `p` exists and satisfies `f`. A `Bool`, so a parser that tests it has a
single failure branch: with two (out of bounds, wrong byte), the compiler joins them through a
heap-allocated `.error` that a surrounding `alt` or `many` must then take apart. -/
@[inline]
def byteIs
    (arr : ByteArray)
    (p : Nat)
    (f : UInt8 → Bool)
    : Bool
    :=
  if h : p < arr.size then f arr[p] else false

/-- A byte that passes `byteIs` is in bounds. -/
theorem lt_of_byteIs
    {arr : ByteArray}
    {p : Nat}
    {f : UInt8 → Bool}
    (h : byteIs arr p f = true)
    : p < arr.size
    := by
  unfold byteIs at h
  split at h
  · assumption
  · nomatch h

/-- In bounds, `byteIs` is `f` applied to the byte. -/
theorem byteIs_of_lt
    {arr : ByteArray}
    {p : Nat}
    {f : UInt8 → Bool}
    (h : p < arr.size)
    : byteIs arr p f = f arr[p]
    := by
  simp only [byteIs, dite_eq_left h]

/-- At or past the end of input, `byteIs` is false. -/
theorem byteIs_of_le
    {arr : ByteArray}
    {p : Nat}
    {f : UInt8 → Bool}
    (h : arr.size ≤ p)
    : byteIs arr p f = false
    := by
  simp only [byteIs, dite_eq_right (Nat.not_lt.mpr h)]

/-- The plain failure at `p`, built out of line. Inlined, its two-field `Err` could take the
reset/reuse cell a caller freed for its success path (the `.ok` after `many` in a `fix` body). -/
@[noinline]
def failAt
    (p : Nat)
    : Err
    :=
  { pos := p }

/-- Consume one byte satisfying `f`, or fail without consuming.
On failure the furthest offset is the current position `p`. -/
@[inline]
def GParser.satisfy
    (f : UInt8 → Bool)
    : GParser conditional UInt8
    where
  run := fun arr p =>
    if h : byteIs arr p f then .ok (arr[p]'(lt_of_byteIs h)) (p + 1) else .error (failAt p)
  cwit := by
    intro arr q a q' heq
    split at heq
    · simp only [ParseResult.ok.injEq] at heq; omega
    · nomatch heq
  ewit := nofun
  swit := nofun
  bwit := by
    intro arr q a q' hq heq
    split at heq
    · rename_i hb
      have := lt_of_byteIs hb
      simp only [ParseResult.ok.injEq] at heq; omega
    · nomatch heq
  fwit := by
    intro arr q e hq heq
    split at heq
    · contradiction
    · simp only [ParseResult.error.injEq] at heq
      subst e
      exact ⟨Nat.le_refl q, hq⟩

/-- Match a specific byte.
On failure the furthest offset is the current position `p`. -/
@[inline]
def GParser.byte
    (c : UInt8)
    : GParser conditional Unit
    where
  run := fun arr p => if byteIs arr p (· == c) then .ok () (p + 1) else .error (failAt p)
  cwit := by
    intro arr q a q' heq
    split at heq
    · simp only [ParseResult.ok.injEq] at heq; omega
    · nomatch heq
  ewit := nofun
  swit := nofun
  bwit := by
    intro arr q a q' hq heq
    split at heq
    · rename_i hb
      have := lt_of_byteIs hb
      simp only [ParseResult.ok.injEq] at heq; omega
    · nomatch heq
  fwit := by
    intro arr q e hq heq
    split at heq
    · contradiction
    · simp only [ParseResult.error.injEq] at heq
      subst e
      exact ⟨Nat.le_refl q, hq⟩

/-- Run `p` and hand the consumed byte range `(arr, start, stop)` to `f` (grade preserved).
Lets a value parser fold over the raw input bytes directly, with no `extract`/`fromUTF8?`/
`String` round-trip; `capture` is the case that decodes the slice as text. -/
@[inline]
def GParser.captureWith
    (f : ByteArray → Nat → Nat → β)
    (p : GParser g α)
    : GParser g β
    where
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
    next e hx => nomatch heq
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
    next e hx => nomatch heq
  fwit := by
    intro arr q e hq heq
    split at heq
    next a q' hp => contradiction
    next e' hp =>
      simp only [ParseResult.error.injEq] at heq
      subst e
      exact p.fwit hq hp

/-- Return the input slice a parser consumed, decoded as text (grade preserved). Lets
combinator parsers build real syntax trees (atom names, identifiers, header fields)
instead of only structural counts. Invalid UTF-8 in the slice decodes to `""`. -/
@[inline]
def GParser.capture
    (p : GParser g α)
    : GParser g String
    :=
  GParser.captureWith (fun arr q q' => (String.fromUTF8? (arr.extract q q')).getD "") p

/-- Like `captureWith`, but `f` may reject the consumed range by returning `none`, in which
case the parse fails at the entry offset. The result grade keeps `p`'s consumption but sets
`errors := possibly` (the extra failure path), so a `conditional` `p` yields a `conditional`
parser. Lets a value decoder veto a syntactically-valid but semantically-out-of-range slice
(e.g. a JSON exponent so large that folding it would blow up). -/
@[inline]
def GParser.captureWith?
    (f : ByteArray → Nat → Nat → Option β)
    (p : GParser g α)
    : GParser ⟨possibly, g.consumes⟩ β
    where
  run := fun arr q =>
    match p.run arr q with
    | .ok _ q' => match f arr q q' with
      | some b => .ok b q'
      | none   => .error { pos := q }
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
      next hf => nomatch heq
    next e hx => nomatch heq
  ewit := nofun
  swit := nofun
  bwit := by
    intro arr q b q' hq heq
    split at heq
    next a p' hx =>
      split at heq
      next b0 hf =>
        simp only [ParseResult.ok.injEq] at heq
        obtain ⟨_, rfl⟩ := heq
        exact p.bwit hq hx
      next hf => nomatch heq
    next e hx => nomatch heq
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
@[inline]
def GParser.dispatch
    (select : UInt8 → GParser conditional α)
    : GParser conditional α
    where
  run := fun arr p => if h : p < arr.size then (select arr[p]).run arr p else .error { pos := p }
  cwit := by
    intro arr q a q' heq
    split at heq
    · exact (select _).cwit heq
    · nomatch heq
  ewit := nofun
  swit := nofun
  bwit := by
    intro arr q a q' hq heq
    split at heq
    · exact (select _).bwit hq heq
    · nomatch heq
  fwit := by
    intro arr q e hq heq
    split at heq
    · exact (select _).fwit hq heq
    · simp only [ParseResult.error.injEq] at heq
      subst e
      exact ⟨Nat.le_refl q, hq⟩

/-- Map over the result (grade preserved). -/
@[inline]
def GParser.map
    (h : α → β)
    (x : GParser g α)
    : GParser g β
    where
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
    next e hx => nomatch heq
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
    next e hx => nomatch heq
  fwit := by
    intro arr q e hq heq
    split at heq
    next a q' hx => contradiction
    next e' hx =>
      simp only [ParseResult.error.injEq] at heq
      subst e
      exact x.fwit hq hx

/-- Monadic bind; grades multiply.
Furthest offset propagates on failure. -/
@[inline]
def GParser.bind
    (x : GParser g α)
    (f : α → GParser g' β)
    : GParser (g * g') β
    where
  run := fun arr p =>
    match x.run arr p with
    | .ok a p' => (f a).run arr p'
    | .error e => .error e
  cwit := by
    intro arr q a q' heq
    split at heq
    next fst p' hx =>
      simpa only [grade_mul_consumes] using cw_seq (x.cwit hx) ((f fst).cwit heq)
    next e hx => nomatch heq
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
      rw [ha] at hx; nomatch hx
  bwit := by
    intro arr q a q' hq heq
    split at heq
    next fst p' hx => exact (f fst).bwit (x.bwit hq hx) heq
    next e hx => nomatch heq
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

/-- Sequence, keeping the right value; grades multiply.
Furthest offset from either `x` or `y` propagates on failure. -/
@[inline]
def GParser.seqR
    (x : GParser g α)
    (y : GParser g' β)
    : GParser (g * g') β
    :=
  GParser.bind x fun _ => y

/-- `seqR` runs `x`, then `y` from where `x` stopped. -/
theorem GParser.seqR_run
    (x : GParser g α)
    (y : GParser g' β)
    (arr : ByteArray)
    (p : Nat)
    : (GParser.seqR x y).run arr p =
        match x.run arr p with
        | .ok _ p' => y.run arr p'
        | .error e => .error e
    :=
  rfl

/-- Sequence, keeping the left value; grades multiply.
Furthest offset propagates on failure. -/
@[inline]
def GParser.seqL
    (x : GParser g α)
    (y : GParser g' β)
    : GParser (g * g') α
    :=
  GParser.bind x fun a => GParser.map (fun _ => a) y

/-- `seqL` runs `x`, then `y`, and keeps `x`'s value. -/
theorem GParser.seqL_run
    (x : GParser g α)
    (y : GParser g' β)
    (arr : ByteArray)
    (p : Nat)
    : (GParser.seqL x y).run arr p =
        match x.run arr p with
        | .ok a p' =>
          match y.run arr p' with
          | .ok _ p'' => .ok a p''
          | .error e  => .error e
        | .error e => .error e
    :=
  rfl

/-- Ordered choice; grade follows `Grade.choice`.
On failure, the two errors are merged furthest-wins (`Err.merge`). -/
@[inline]
def GParser.alt
    (x : GParser ⟨ge, gc⟩ α)
    (y : GParser ⟨ge', gc'⟩ α)
    : GParser ⟨min ge ge', ge.ite gc' gc⟩ α
    where
  run := fun arr p =>
    match x.run arr p with
    | .ok a p' => .ok a p'
    | .error ex =>
      match y.run arr p with
      | .ok a p' => .ok a p'
      | .error ey => .error (ex.merge ey)
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
      · -- Both branches failed, so the result is the merged error.
        nomatch heq
  ewit := by
    intro he arr q
    simp only [Modality.min_always] at he
    obtain ⟨he1, he2⟩ := he
    obtain ⟨ex, hex⟩ := x.ewit he1 arr q
    obtain ⟨ey, hey⟩ := y.ewit he2 arr q
    exact ⟨ex.merge ey, by simp only [hex, hey]⟩
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
          rw [ha] at hx; nomatch hx
        · obtain ⟨a, q', ha⟩ := y.swit hg arr q
          rw [ha] at hy; nomatch hy
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
      · nomatch heq
  fwit := by
    intro arr q e hq heq
    split at heq
    · contradiction
    · rename_i ex hx
      split at heq
      · contradiction
      · rename_i ey hy
        simp only [ParseResult.error.injEq] at heq
        subst e
        rcases Err.merge_pos ex ey with h | h <;> rw [h]
        · exact x.fwit hq hx
        · exact y.fwit hq hy

/-- Apply a binary function across two parses; grades multiply.
Furthest offset propagates on failure. -/
@[inline]
def GParser.map2
    {γ : Type}
    (f : α → β → γ)
    (x : GParser g α)
    (y : GParser g' β)
    : GParser (g * g') γ
    :=
  GParser.bind x fun a => GParser.map (f a) y

/-- `map2` runs `x`, then `y`, and combines both values with `f`. -/
theorem GParser.map2_run
    {γ : Type}
    (f : α → β → γ)
    (x : GParser g α)
    (y : GParser g' β)
    (arr : ByteArray)
    (p : Nat)
    : (GParser.map2 f x y).run arr p =
        match x.run arr p with
        | .ok a p' =>
          match y.run arr p' with
          | .ok b p'' => .ok (f a b) p''
          | .error e  => .error e
        | .error e => .error e
    :=
  rfl

/-- Consume exactly `n` bytes if available.
On failure the furthest offset is the current position. -/
@[inline]
def GParser.takeN
    (n : Nat)
    : GParser fallible Unit
    where
  run := fun arr p => if p + n ≤ arr.size then .ok () (p + n) else .error { pos := p }
  cwit := by
    intro arr q a q' heq
    split at heq
    · simp only [ParseResult.ok.injEq] at heq; omega
    · nomatch heq
  ewit := nofun
  swit := nofun
  bwit := by
    intro arr q a q' hq heq
    split at heq
    · simp only [ParseResult.ok.injEq] at heq; omega
    · nomatch heq
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
@[inline]
def GParser.label
    (name : String)
    (p : GParser g α)
    : GParser g α
    where
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
    · nomatch h
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
    · nomatch h
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

end Grip
