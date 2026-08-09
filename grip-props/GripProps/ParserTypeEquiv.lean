/-
Copyright (c) 2026 Jonathan Cubides. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Prieto-Cubides
-/
import Grip
import Mathlib.Logic.Equiv.Defs

set_option autoImplicit false

open Modality Grade

namespace EquivAudit

/-!
# `GParser` / PrimParser carrier audit

The PrimParser structures below reproduce the position-relevant fragment of
`PrimParser.Basic` at commit `d33728c09bc66ec0853512abc89cbc57ba007532`.
Its grade definitions have the same three-constructor structure and algebra as
Grip's, so the model reuses Grip's after the mechanical constructor renaming;
this also avoids duplicate global declarations.

The current `GParser` is not used as the left side of the final isomorphism: although
failures from valid starts are now bounded, `run` still accepts invalid starting offsets.
`SizedGParser` moves that remaining invariant into the input. `sizedParserEquiv` then gives
executable maps in both directions and proves both round trips using Lean's standard `Equiv`.
-/

/-! A namespaced copy of the relevant PrimParser carrier, using Grip's structurally
identical Grade/Modality after constructor renaming so both representations coexist. -/
namespace Prim

structure Text (n : Nat) where
  bytes : ByteArray
  valid : n ≤ bytes.size

abbrev Text.pos {n : Nat} (t : Text n) : Nat := t.bytes.size - n

@[ext] theorem Text.ext {n : Nat} {a b : Text n} (h : a.bytes = b.bytes) : a = b := by
  cases a
  cases b
  cases h
  rfl

structure Success (n : Nat) (consumes : Modality) (α : Type) where
  result : α
  restSize : Nat
  witness : consumptionWitness restSize n consumes

@[ext] theorem Success.ext {n : Nat} {c : Modality} {α : Type}
    {a b : Success n c α}
    (hr : a.result = b.result) (hs : a.restSize = b.restSize) : a = b := by
  cases a
  cases b
  cases hr
  cases hs
  rfl

structure Failure (n : Nat) (ε : Type) where
  error : ε
  restSize : Nat
  witness : restSize ≤ n

@[ext] theorem Failure.ext {n : Nat} {ε : Type}
    {a b : Failure n ε}
    (he : a.error = b.error) (hs : a.restSize = b.restSize) : a = b := by
  cases a
  cases b
  cases he
  cases hs
  rfl

inductive Outcome (ε : Type) (n : Nat) (consumes : Modality) (α : Type) where
  | failure : Failure n ε → Outcome ε n consumes α
  | success : Success n consumes α → Outcome ε n consumes α

def Outcome.Sound {ε : Type} {n : Nat} {c : Modality} {α : Type}
    (errors : Modality) (o : Outcome ε n c α) : Prop :=
  match o with
  | .failure _ => possibly ≤ errors
  | .success _ => errors ≤ possibly

structure Parser (ε : Type) (g : Grade) (α : Type) where
  run : ∀ {n : Nat}, Text n → Outcome ε n g.consumes α
  sound : ∀ {n : Nat} (t : Text n), Outcome.Sound g.errors (run t)

@[ext] theorem Parser.ext {ε : Type} {g : Grade} {α : Type}
    {p q : Parser ε g α}
    (h : ∀ {n : Nat} (t : Text n), p.run t = q.run t) : p = q := by
  obtain ⟨pr, ps⟩ := p
  obtain ⟨qr, qs⟩ := q
  have hr : @pr = @qr := by funext n t; exact h t
  subst hr
  rfl

end Prim

open Grip

/-! ## Why the current carrier is too large -/

namespace Current

/-- Equality of observable runs when the starting offset is valid. -/
def ValidRunEq {g : Grade} {α : Type} (p q : GParser g α) : Prop :=
  ∀ (arr : ByteArray) (pos : Nat), pos ≤ arr.size → p.run arr pos = q.run arr pos

def zeroOutside : GParser pure Bool where
  run := fun _ q => .ok false q
  cwit := by intro arr q a q' h; cases h; rfl
  ewit := by intro h; exact Modality.noConfusion h
  swit := by intro _ arr q; exact ⟨false, q, rfl⟩
  bwit := by intro arr q a q' hq h; cases h; exact hq
  fwit := by intro arr q e hq h; contradiction

def signalOutside : GParser pure Bool where
  run := fun arr q => .ok (decide (arr.size < q)) q
  cwit := by intro arr q a q' h; cases h; rfl
  ewit := by intro h; exact Modality.noConfusion h
  swit := by intro _ arr q; exact ⟨decide (arr.size < q), q, rfl⟩
  bwit := by intro arr q a q' hq h; cases h; exact hq
  fwit := by intro arr q e hq h; contradiction

/-- PrimParser cannot observe the distinction between these parsers because its
`Text n` input represents only valid starting offsets. -/
theorem same_on_valid_inputs : ValidRunEq zeroOutside signalOutside := by
  intro arr q hq
  simp [zeroOutside, signalOutside, Nat.not_lt.mpr hq]

theorem different_as_GParser : zeroOutside ≠ signalOutside := by
  intro h
  have hr := congrArg (fun p => p.run ByteArray.empty 1) h
  simp [zeroOutside, signalOutside] at hr

/-- The former future-position counterexample is now excluded by the carrier itself. -/
theorem failure_in_bounds {g : Grade} {α : Type} (p : GParser g α)
    {arr : ByteArray} {q : Nat} {e : Err} (hq : q ≤ arr.size)
    (h : p.run arr q = .error e) : q ≤ e.pos ∧ e.pos ≤ arr.size :=
  p.fwit hq h

end Current

/-! Minimal repaired offset representation:
* callers provide an erased proof that the start offset is in bounds;
* failures prove that their absolute position lies between start and EOF.
The runtime data remains `ByteArray → Nat → ParseResult α`. -/
structure SafeGParser (g : Grade) (α : Type) where
  run : ∀ (arr : ByteArray) (q : Nat), q ≤ arr.size → ParseResult α
  cwit : ∀ {arr q} (hq : q ≤ arr.size) {a q'},
    run arr q hq = .ok a q' → consumptionWitness q q' g.consumes
  ewit : g.errors = always → ∀ arr q (hq : q ≤ arr.size),
    ∃ e : Err, run arr q hq = .error e
  swit : g.errors = never → ∀ arr q (hq : q ≤ arr.size),
    ∃ a q', run arr q hq = .ok a q'
  bwit : ∀ {arr q} (hq : q ≤ arr.size) {a q'},
    run arr q hq = .ok a q' → q' ≤ arr.size
  fwit : ∀ {arr q} (hq : q ≤ arr.size) {e},
    run arr q hq = .error e → q ≤ e.pos ∧ e.pos ≤ arr.size

@[ext] theorem SafeGParser.ext {g : Grade} {α : Type}
    {p q : SafeGParser g α}
    (h : ∀ (arr : ByteArray) (pos : Nat) (hp : pos ≤ arr.size),
      p.run arr pos hp = q.run arr pos hp) : p = q := by
  obtain ⟨pr, pc, pe, ps, pb, pf⟩ := p
  obtain ⟨qr, qc, qe, qs, qb, qf⟩ := q
  have hr : @pr = @qr := by funext arr pos hp; exact h arr pos hp
  subst hr
  rfl

theorem SafeGParser.run_congr {g : Grade} {α : Type} (p : SafeGParser g α)
    {arr : ByteArray} {q q' : Nat} (h : q = q')
    (hq : q ≤ arr.size) (hq' : q' ≤ arr.size) :
    p.run arr q hq = p.run arr q' hq' := by
  subst q'
  rfl

private theorem toRestWitness {c : Modality} {n q' : Nat}
    (t : Prim.Text n)
    (hc : consumptionWitness t.pos q' c)
    (hq' : q' ≤ t.bytes.size) :
    consumptionWitness (t.bytes.size - q') n c := by
  have hv := t.valid
  simp only [Prim.Text.pos] at hc
  cases c <;> simp only [consumptionWitness] at hc ⊢ <;> omega

private theorem fromRestWitness {c : Modality} {α : Type}
    {arr : ByteArray} {q : Nat} (hq : q ≤ arr.size)
    (s : Prim.Success (arr.size - q) c α) :
    consumptionWitness q (arr.size - s.restSize) c := by
  have hw := s.witness
  cases c <;> simp only [consumptionWitness] at hw ⊢ <;> omega

def toPrim {g : Grade} {α : Type} (p : SafeGParser g α) :
    Prim.Parser (List String) g α where
  run {n} t :=
    let q := t.pos
    have hq : q ≤ t.bytes.size := Nat.sub_le ..
    match h : p.run t.bytes q hq with
    | .ok a q' =>
      .success {
        result := a
        restSize := t.bytes.size - q'
        witness := toRestWitness t (p.cwit hq h) (p.bwit hq h)
      }
    | .error e =>
      .failure {
        error := e.expected
        restSize := t.bytes.size - e.pos
        witness := by
          have he := (p.fwit hq h).1
          change t.bytes.size - n ≤ e.pos at he
          omega
      }
  sound {n} t := by
    simp only []
    split
    next a q' h =>
      show g.errors ≤ possibly
      apply Modality.le_possibly_of_ne_always
      intro hg
      obtain ⟨e, he⟩ := p.ewit hg t.bytes t.pos (by
        simp only [Prim.Text.pos]
        omega)
      rw [he] at h
      contradiction
    next e h =>
      show possibly ≤ g.errors
      apply Modality.possibly_le_of_ne_never
      intro hg
      obtain ⟨a, q', hs⟩ := p.swit hg t.bytes t.pos (by
        simp only [Prim.Text.pos]
        omega)
      rw [hs] at h
      contradiction

def fromPrim {g : Grade} {α : Type} (p : Prim.Parser (List String) g α) :
    SafeGParser g α where
  run arr q hq :=
    let t : Prim.Text (arr.size - q) := ⟨arr, by omega⟩
    match p.run t with
    | .success s => .ok s.result (arr.size - s.restSize)
    | .failure f => .error ⟨arr.size - f.restSize, f.error⟩
  cwit := by
    intro arr q hq a q' h
    simp only [] at h
    split at h
    next s hs =>
      simp only [ParseResult.ok.injEq] at h
      obtain ⟨_, rfl⟩ := h
      exact fromRestWitness hq s
    next f hf => contradiction
  ewit := by
    intro hg arr q hq
    simp only []
    cases h : p.run (Prim.Text.mk arr (by omega : arr.size - q ≤ arr.size)) with
    | failure f => exact ⟨⟨arr.size - f.restSize, f.error⟩, rfl⟩
    | success s =>
      have hs := p.sound (Prim.Text.mk arr (by omega : arr.size - q ≤ arr.size))
      rw [h] at hs
      simp only [Prim.Outcome.Sound, hg] at hs
      contradiction
  swit := by
    intro hg arr q hq
    simp only []
    cases h : p.run (Prim.Text.mk arr (by omega : arr.size - q ≤ arr.size)) with
    | success s => exact ⟨s.result, arr.size - s.restSize, rfl⟩
    | failure f =>
      have hs := p.sound (Prim.Text.mk arr (by omega : arr.size - q ≤ arr.size))
      rw [h] at hs
      simp only [Prim.Outcome.Sound, hg] at hs
      contradiction
  bwit := by
    intro arr q hq a q' h
    simp only [] at h
    split at h
    next s hs =>
      simp only [ParseResult.ok.injEq] at h
      obtain ⟨_, rfl⟩ := h
      omega
    next f hf => contradiction
  fwit := by
    intro arr q hq e h
    simp only [] at h
    split at h
    next s hs => contradiction
    next f hf =>
      simp only [ParseResult.error.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have hw := f.witness
      change q ≤ arr.size - f.restSize ∧ arr.size - f.restSize ≤ arr.size
      constructor <;> omega

theorem fromPrim_toPrim_run {g : Grade} {α : Type}
    (p : SafeGParser g α) (arr : ByteArray) (q : Nat) (hq : q ≤ arr.size) :
    (fromPrim (toPrim p)).run arr q hq = p.run arr q hq := by
  let t : Prim.Text (arr.size - q) := ⟨arr, by omega⟩
  change
    (match (toPrim p).run t with
     | .success s => .ok s.result (arr.size - s.restSize)
     | .failure f => .error ⟨arr.size - f.restSize, f.error⟩) = p.run arr q hq
  unfold toPrim
  dsimp only
  have ht : t.pos = q := by
    dsimp only [t, Prim.Text.pos]
    exact Nat.sub_sub_self hq
  have hrun : p.run t.bytes t.pos (Nat.sub_le ..) = p.run arr q hq :=
    p.run_congr ht (Nat.sub_le ..) hq
  split
  next s heq =>
    split at heq
    next a q' h =>
      simp only [Prim.Outcome.success.injEq] at heq
      subst s
      have h' : p.run arr q hq = .ok a q' := by
        rw [← hrun]
        exact h
      rw [h']
      have hb := p.bwit hq h'
      change ParseResult.ok a (arr.size - (arr.size - q')) = ParseResult.ok a q'
      rw [Nat.sub_sub_self hb]
    next e h => contradiction
  next f heq =>
    split at heq
    next a q' h => contradiction
    next e h =>
      simp only [Prim.Outcome.failure.injEq] at heq
      subst f
      have h' : p.run arr q hq = .error e := by
        rw [← hrun]
        exact h
      rw [h']
      have hb := (p.fwit hq h').2
      change ParseResult.error ⟨arr.size - (arr.size - e.pos), e.expected⟩ = ParseResult.error e
      rw [Nat.sub_sub_self hb]

theorem fromPrim_toPrim {g : Grade} {α : Type}
    (p : SafeGParser g α) : fromPrim (toPrim p) = p := by
  apply SafeGParser.ext
  exact fromPrim_toPrim_run p

/-! A sized-input repair gives a literal isomorphism without quotienting away
out-of-bounds calls. It keeps Grip's flat `ParseResult`, absolute offsets, and
erased witnesses; only the valid start state moves into the input type. -/

structure SizedGParser (g : Grade) (α : Type) where
  run : ∀ {n : Nat}, Prim.Text n → ParseResult α
  cwit : ∀ {n : Nat} {t : Prim.Text n} {a q'},
    run t = .ok a q' → consumptionWitness t.pos q' g.consumes
  ewit : g.errors = always → ∀ {n : Nat} (t : Prim.Text n),
    ∃ e : Err, run t = .error e
  swit : g.errors = never → ∀ {n : Nat} (t : Prim.Text n),
    ∃ a q', run t = .ok a q'
  bwit : ∀ {n : Nat} {t : Prim.Text n} {a q'},
    run t = .ok a q' → q' ≤ t.bytes.size
  fwit : ∀ {n : Nat} {t : Prim.Text n} {e},
    run t = .error e → t.pos ≤ e.pos ∧ e.pos ≤ t.bytes.size

@[ext] theorem SizedGParser.ext {g : Grade} {α : Type}
    {p q : SizedGParser g α}
    (h : ∀ {n : Nat} (t : Prim.Text n), p.run t = q.run t) : p = q := by
  obtain ⟨pr, pc, pe, ps, pb, pf⟩ := p
  obtain ⟨qr, qc, qe, qs, qb, qf⟩ := q
  have hr : @pr = @qr := by funext n t; exact h t
  subst hr
  rfl

private theorem fromRestWitnessText {c : Modality} {n : Nat} {α : Type}
    (t : Prim.Text n) (s : Prim.Success n c α) :
    consumptionWitness t.pos (t.bytes.size - s.restSize) c := by
  have hw := s.witness
  have hv := t.valid
  simp only [Prim.Text.pos]
  cases c <;> simp only [consumptionWitness] at hw ⊢ <;> omega

def outcomeOfSized {g : Grade} {α : Type} (p : SizedGParser g α)
    {n : Nat} (t : Prim.Text n) : Prim.Outcome (List String) n g.consumes α :=
  match h : p.run t with
  | .ok a q' =>
    .success {
      result := a
      restSize := t.bytes.size - q'
      witness := toRestWitness t (p.cwit h) (p.bwit h)
    }
  | .error e =>
    .failure {
      error := e.expected
      restSize := t.bytes.size - e.pos
      witness := by
        have he := (p.fwit h).1
        simp only [Prim.Text.pos] at he
        omega
    }

def sizedToPrim {g : Grade} {α : Type} (p : SizedGParser g α) :
    Prim.Parser (List String) g α where
  run t := outcomeOfSized p t
  sound {n} t := by
    simp only [outcomeOfSized]
    split
    next a q' h =>
      show g.errors ≤ possibly
      apply Modality.le_possibly_of_ne_always
      intro hg
      obtain ⟨e, he⟩ := p.ewit hg t
      rw [he] at h
      contradiction
    next e h =>
      show possibly ≤ g.errors
      apply Modality.possibly_le_of_ne_never
      intro hg
      obtain ⟨a, q', hs⟩ := p.swit hg t
      rw [hs] at h
      contradiction

def resultOfPrim {g : Grade} {α : Type} (p : Prim.Parser (List String) g α)
    {n : Nat} (t : Prim.Text n) : ParseResult α :=
  match p.run t with
  | .success s => .ok s.result (t.bytes.size - s.restSize)
  | .failure f => .error ⟨t.bytes.size - f.restSize, f.error⟩

def primToSized {g : Grade} {α : Type} (p : Prim.Parser (List String) g α) :
    SizedGParser g α where
  run t := resultOfPrim p t
  cwit := by
    intro n t a q' h
    simp only [resultOfPrim] at h
    split at h
    next s hs =>
      simp only [ParseResult.ok.injEq] at h
      obtain ⟨_, rfl⟩ := h
      exact fromRestWitnessText t s
    next f hf => contradiction
  ewit := by
    intro hg n t
    simp only [resultOfPrim]
    cases h : p.run t with
    | failure f => exact ⟨⟨t.bytes.size - f.restSize, f.error⟩, rfl⟩
    | success s =>
      have hs := p.sound t
      rw [h] at hs
      simp only [Prim.Outcome.Sound, hg] at hs
      contradiction
  swit := by
    intro hg n t
    simp only [resultOfPrim]
    cases h : p.run t with
    | success s => exact ⟨s.result, t.bytes.size - s.restSize, rfl⟩
    | failure f =>
      have hs := p.sound t
      rw [h] at hs
      simp only [Prim.Outcome.Sound, hg] at hs
      contradiction
  bwit := by
    intro n t a q' h
    simp only [resultOfPrim] at h
    split at h
    next s hs =>
      simp only [ParseResult.ok.injEq] at h
      obtain ⟨_, rfl⟩ := h
      omega
    next f hf => contradiction
  fwit := by
    intro n t e h
    simp only [resultOfPrim] at h
    split at h
    next s hs => contradiction
    next f hf =>
      simp only [ParseResult.error.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have hw := f.witness
      have hv := t.valid
      simp only [Prim.Text.pos]
      constructor <;> omega

theorem primToSized_sizedToPrim_run {g : Grade} {α : Type}
    (p : SizedGParser g α) {n : Nat} (t : Prim.Text n) :
    resultOfPrim (sizedToPrim p) t = p.run t := by
  unfold resultOfPrim
  dsimp only [sizedToPrim]
  unfold outcomeOfSized
  split
  next s heq =>
    split at heq
    next a q' h =>
      simp only [Prim.Outcome.success.injEq] at heq
      subst s
      calc
        _ = ParseResult.ok a q' := by
          have hb := p.bwit h
          change ParseResult.ok a (t.bytes.size - (t.bytes.size - q')) = ParseResult.ok a q'
          rw [Nat.sub_sub_self hb]
        _ = p.run t := h.symm
    next e h => contradiction
  next f heq =>
    split at heq
    next a q' h => contradiction
    next e h =>
      simp only [Prim.Outcome.failure.injEq] at heq
      subst f
      calc
        _ = ParseResult.error e := by
          have hb := (p.fwit h).2
          change ParseResult.error ⟨t.bytes.size - (t.bytes.size - e.pos), e.expected⟩ =
            ParseResult.error e
          rw [Nat.sub_sub_self hb]
        _ = p.run t := h.symm

theorem primToSized_sizedToPrim {g : Grade} {α : Type}
    (p : SizedGParser g α) : primToSized (sizedToPrim p) = p := by
  apply SizedGParser.ext
  exact primToSized_sizedToPrim_run p

theorem sizedToPrim_primToSized_run {g : Grade} {α : Type}
    (p : Prim.Parser (List String) g α) {n : Nat} (t : Prim.Text n) :
    outcomeOfSized (primToSized p) t = p.run t := by
  cases h : p.run t with
  | success s =>
      unfold outcomeOfSized
      split
      next a q' heq =>
        have hr : (primToSized p).run t =
            ParseResult.ok s.result (t.bytes.size - s.restSize) := by
          simp only [primToSized, resultOfPrim, h]
        rw [hr] at heq
        simp only [ParseResult.ok.injEq] at heq
        obtain ⟨rfl, rfl⟩ := heq
        calc
          _ = Prim.Outcome.success s := by
            have hb : s.restSize ≤ t.bytes.size :=
              Nat.le_trans s.witness.le t.valid
            apply congrArg (fun x : Prim.Success n g.consumes α => Prim.Outcome.success x)
            apply Prim.Success.ext
            · rfl
            · exact Nat.sub_sub_self hb
          _ = p.run t := h.symm
        case calc.step => exact h
      next e heq =>
        have hr : (primToSized p).run t =
            ParseResult.ok s.result (t.bytes.size - s.restSize) := by
          simp only [primToSized, resultOfPrim, h]
        rw [hr] at heq
        contradiction
  | failure f =>
      unfold outcomeOfSized
      split
      next a q' heq =>
        have hr : (primToSized p).run t =
            ParseResult.error ⟨t.bytes.size - f.restSize, f.error⟩ := by
          simp only [primToSized, resultOfPrim, h]
        rw [hr] at heq
        contradiction
      next e heq =>
        have hr : (primToSized p).run t =
            ParseResult.error ⟨t.bytes.size - f.restSize, f.error⟩ := by
          simp only [primToSized, resultOfPrim, h]
        rw [hr] at heq
        simp only [ParseResult.error.injEq] at heq
        subst e
        calc
          _ = Prim.Outcome.failure f := by
            have hb : f.restSize ≤ t.bytes.size := Nat.le_trans f.witness t.valid
            apply congrArg (fun x : Prim.Failure n (List String) =>
              (Prim.Outcome.failure x : Prim.Outcome (List String) n g.consumes α))
            apply Prim.Failure.ext
            · rfl
            · exact Nat.sub_sub_self hb
          _ = p.run t := h.symm
        case calc.step => exact h

theorem sizedToPrim_primToSized {g : Grade} {α : Type}
    (p : Prim.Parser (List String) g α) : sizedToPrim (primToSized p) = p := by
  apply Prim.Parser.ext
  exact sizedToPrim_primToSized_run p

def sizedParserEquiv (g : Grade) (α : Type) :
    Equiv (SizedGParser g α) (Prim.Parser (List String) g α) where
  toFun := sizedToPrim
  invFun := primToSized
  left_inv := primToSized_sizedToPrim
  right_inv := sizedToPrim_primToSized

end EquivAudit
