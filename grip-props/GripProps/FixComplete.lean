/-
Copyright (c) 2026 Jonathan Cubides. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Cubides
-/
import Grip

/-!
# Completeness of the fuel bound

`GParser.fix` runs its body on a fuel bounded by the bytes remaining, `arr.size - q + 1`
(`Grip/Graded.lean`). This file proves that bound is *complete*: it truncates no parse that a
larger fuel would accept, so `fix` computes the ideal fixpoint on every grammar it should.

The hypothesis that makes this work is **guardedness** (`Guarded`): the body's output at offset
`q` depends on its self-reference only at strictly greater offsets. Every grammar that consumes
at least one byte before recurring satisfies it -- and the `conditional` consumption grade is
exactly what forces that consumption. The negative-lookahead body `notFollowedBy self` does not
satisfy it (it inspects `self` at the same offset), and indeed no fuel bound tames such a body:
its result can flip with the fuel's parity.

Because error payloads record the *furthest* offset any branch reached, they can legitimately
grow with more fuel; completeness is therefore stated up to `AgreeOk`, agreement on the accepted
value (the `ok` outcome), which is exactly what "no parse is truncated" means.
-/

open Grip

namespace Grip.FixComplete

variable {α : Type}

/-! ### Agreement on acceptance -/

/-- Two results agree on acceptance: same `ok` value and offset, or both failures (whose error
payloads may differ, since they record the furthest offset reached). -/
def AgreeOk : ParseResult α → ParseResult α → Prop
  | .ok a q', .ok b q'' => a = b ∧ q' = q''
  | .ok _ _, .error _ => False
  | .error _, .ok _ _ => False
  | .error _, .error _ => True

theorem AgreeOk.refl : ∀ r : ParseResult α, AgreeOk r r := by
  intro r; cases r <;> simp [AgreeOk]

theorem AgreeOk.symm {r₁ r₂ : ParseResult α} (h : AgreeOk r₁ r₂) : AgreeOk r₂ r₁ := by
  cases r₁ <;> cases r₂ <;> simp_all [AgreeOk]

theorem AgreeOk.trans {r₁ r₂ r₃ : ParseResult α}
    (h₁ : AgreeOk r₁ r₂) (h₂ : AgreeOk r₂ r₃) : AgreeOk r₁ r₃ := by
  cases r₁ <;> cases r₂ <;> cases r₃ <;> simp_all [AgreeOk]

/-- Acceptance agreement propagates through the advance clamp. -/
theorem clamp_agree {r₁ r₂ : ParseResult α} (arr : ByteArray) (q : Nat)
    (h : AgreeOk r₁ r₂) : AgreeOk (clampAdvance arr q r₁) (clampAdvance arr q r₂) := by
  cases r₁ with
  | ok a q' => cases r₂ with
    | ok b q'' => simp only [AgreeOk] at h; obtain ⟨ha, hq⟩ := h; subst ha; subst hq
                  exact AgreeOk.refl _
    | error e => exact (h : False).elim
  | error e => cases r₂ with
    | ok b q'' => exact (h : False).elim
    | error e' => exact True.intro

/-- Past the end of input the clamp can never yield `ok`, so any two clamped results agree
(both are failures), whatever is being clamped. -/
theorem clamp_oob {r₁ r₂ : ParseResult α} (arr : ByteArray) (q : Nat) (hq : arr.size ≤ q) :
    AgreeOk (clampAdvance arr q r₁) (clampAdvance arr q r₂) := by
  have oob : ∀ r : ParseResult α, ∃ e, clampAdvance arr q r = .error e := by
    intro r
    cases r with
    | error e => exact ⟨e, rfl⟩
    | ok x q'' =>
      simp only [clampAdvance]
      split
      · rename_i hc; obtain ⟨h1, h2⟩ := hc; omega
      · exact ⟨_, rfl⟩
  obtain ⟨e₁, h₁⟩ := oob r₁
  obtain ⟨e₂, h₂⟩ := oob r₂
  rw [h₁, h₂]; exact True.intro

/-! ### Guardedness and completeness -/

/-- The body `f` is **guarded**: its output at offset `q` depends on its self-reference only at
strictly greater offsets. Stated up to `AgreeOk`, matching the completeness conclusion. Every
consume-before-recurring grammar satisfies this; `notFollowedBy self` does not. -/
def Guarded (f : GParser conditional α → GParser conditional α) : Prop :=
  ∀ (s₁ s₂ : GParser conditional α) (arr : ByteArray) (q : Nat),
    (∀ q', q < q' → AgreeOk (s₁.run arr q') (s₂.run arr q')) →
    AgreeOk ((f s₁).run arr q) ((f s₂).run arr q)

/-- One fuel step is invisible once the fuel already covers the bytes remaining: for a guarded
body, `fixFuel f m` and `fixFuel f (m+1)` accept the same parses whenever `arr.size - q < m`.
Proved by strong recursion on the bytes remaining `arr.size - q`: the body consults its self only
at offsets `q' > q`, where either the offset is out of bounds (the clamp fails, so the two agree)
or `arr.size - q' < arr.size - q` and the induction hypothesis applies. -/
theorem step (f : GParser conditional α → GParser conditional α) (hf : Guarded f)
    (arr : ByteArray) (q m : Nat) (hm : arr.size - q < m) :
    AgreeOk (GParser.fixFuel f m arr q) (GParser.fixFuel f (m + 1) arr q) := by
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  rw [GParser.fixFuel_succ, GParser.fixFuel_succ]
  apply hf
  intro q' hqq'
  rw [GParser.fixSelf_run, GParser.fixSelf_run]
  by_cases hb : q' ≤ arr.size
  · apply clamp_agree
    exact step f hf arr q' m' (by omega)
  · exact clamp_oob arr q' (by omega)
termination_by arr.size - q
decreasing_by omega

/-- Above the bytes-remaining bound all fuels accept the same parses: for a guarded body, every
`fixFuel f (arr.size - q + 1 + k)` accepts exactly what `fixFuel f (arr.size - q + 1)` does. -/
theorem agree_add (f : GParser conditional α → GParser conditional α) (hf : Guarded f)
    (arr : ByteArray) (q : Nat) :
    ∀ k, AgreeOk (GParser.fixFuel f (arr.size - q + 1 + k) arr q)
      (GParser.fixFuel f (arr.size - q + 1) arr q) := by
  intro k
  induction k with
  | zero => exact AgreeOk.refl _
  | succ j ih =>
    have hstep := step f hf arr q (arr.size - q + 1 + j) (by omega)
    exact hstep.symm.trans ih

/-- **Completeness of the fuel bound.** For a guarded body, the fuel `fix` uses,
`arr.size - q + 1`, accepts every parse any larger fuel would: no accepted parse is truncated.
The consumption grade supplies guardedness, so `fix` computes the ideal fixpoint. -/
theorem fixFuel_complete (f : GParser conditional α → GParser conditional α) (hf : Guarded f)
    (arr : ByteArray) (q : Nat) {m : Nat} (hm : arr.size - q + 1 ≤ m) {a : α} {q' : Nat}
    (h : GParser.fixFuel f m arr q = .ok a q') :
    GParser.fixFuel f (arr.size - q + 1) arr q = .ok a q' := by
  have hag := agree_add f hf arr q (m - (arr.size - q + 1))
  have hmB : arr.size - q + 1 + (m - (arr.size - q + 1)) = m := by omega
  rw [hmB, h] at hag
  cases hB : GParser.fixFuel f (arr.size - q + 1) arr q with
  | error e => rw [hB] at hag; exact (hag : False).elim
  | ok b q'' =>
    rw [hB] at hag
    simp only [AgreeOk] at hag
    obtain ⟨ha, hq⟩ := hag
    rw [ha, hq]

/-- **`fix` computes the ideal fixpoint.** For a guarded body and an in-bounds offset, a success
found by any larger fuel is also produced by `fix` itself, whose fuel is `arr.size - q + 1`. So
the fuel bound `fix` uses never truncates an accepted parse. -/
theorem fix_complete (f : GParser conditional α → GParser conditional α) (hf : Guarded f)
    (arr : ByteArray) (q : Nat) (hq : q ≤ arr.size) {m : Nat} (hm : arr.size - q + 1 ≤ m)
    {a : α} {q' : Nat} (h : GParser.fixFuel f m arr q = .ok a q') :
    (GParser.fix f).run arr q = .ok a q' := by
  have hB := fixFuel_complete f hf arr q hm h
  have hs : GParser.fixFuel f (arr.size - q + 1) arr q
      = (f (GParser.fixSelf f (arr.size - q))).run arr q :=
    GParser.fixFuel_succ f (arr.size - q) arr q
  have hB' := hs ▸ hB
  have hcw := (f (GParser.fixSelf f (arr.size - q))).cwit hB'
  have hbw := (f (GParser.fixSelf f (arr.size - q))).bwit hq hB'
  show clampAdvance arr q (GParser.fixFuel f (arr.size - q + 1) arr q) = .ok a q'
  rw [hB]; simp only [clampAdvance]; rw [if_pos ⟨hcw, hbw⟩]

/-! ### The consumption grade forces guardedness

A body that consults its self-reference only *after* a `conditional` (always-consuming) parser
is guarded: the consumed byte pushes the recursive call to a strictly greater offset. This is the
formal content of "the grade forces guardedness". -/

/-- Prepending a `conditional` consumer to a body makes it guarded. `seqR p (k rec)` runs `p`
first; a success advances past `q` (`p.cwit`), so `k rec` -- and hence `rec` -- is consulted only
at offsets `> q`. Guardedness of `k` at those offsets carries the rest. -/
theorem guarded_seqR {β : Type} (p : GParser conditional β)
    (k : GParser conditional α → GParser conditional α) (hk : Guarded k) :
    Guarded (fun rec => GParser.seqR p (k rec)) := by
  intro s₁ s₂ arr q hpre
  simp only [GParser.seqR]
  cases hp : p.run arr q with
  | error e => exact AgreeOk.refl _
  | ok x q' =>
    have hadv : q < q' := p.cwit hp
    exact hk s₁ s₂ arr q' (fun q'' hlt => hpre q'' (by omega))

/-- A body that ignores its self-reference is guarded (its output does not depend on `rec` at
all), the base case for building guarded bodies compositionally. -/
theorem guarded_const (c : GParser conditional α) : Guarded (fun _ => c) := by
  intro _ _ _ _ _; exact AgreeOk.refl _

/-! ### Guardedness is necessary

A body that inspects `self` at the *same* offset -- as negative lookahead (`notFollowedBy self`)
does -- is not guarded, and then no fuel bound is complete: acceptance depends on the fuel's
parity. `oscBody` is the minimal witness. -/

/-- Inverts its self-reference's verdict, guarded by an in-bounds check so `bwit` still holds. It
consults `self` at the same offset, so it is not `Guarded`. -/
def oscBody (self : GParser conditional Unit) : GParser conditional Unit where
  run arr q :=
    if q < arr.size then
      (match self.run arr q with | .ok _ _ => .error ⟨q, []⟩ | .error _ => .ok () (q + 1))
    else .error ⟨q, []⟩
  cwit := by
    intro arr q a q' h
    split at h
    · split at h
      · exact absurd h (by simp)
      · simp only [ParseResult.ok.injEq] at h; omega
    · exact absurd h (by simp)
  ewit := by intro he; exact absurd he (by decide)
  swit := by intro he; exact absurd he (by decide)
  bwit := by
    intro arr q a q' _hq h
    split at h
    · split at h
      · exact absurd h (by simp)
      · simp only [ParseResult.ok.injEq] at h; omega
    · exact absurd h (by simp)

-- Acceptance flips with the fuel's parity: fuel 2 rejects, fuel 3 accepts at offset 1. No single
-- fuel bound is complete for this non-guarded body, so `fixFuel_complete` genuinely needs `Guarded`.
#guard (match GParser.fixFuel oscBody 2 (String.toUTF8 "ab") 0 with | .error _ => true | _ => false)
#guard (match GParser.fixFuel oscBody 3 (String.toUTF8 "ab") 0 with | .ok _ q => q == 1 | _ => false)

end Grip.FixComplete
