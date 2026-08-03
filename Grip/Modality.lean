/-
Copyright (c) 2026 Jonathan Cubides. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Prieto-Cubides

Adapted from PrimParser/Necessity.lean in prim-parser by Jan Mas Rovira
(https://github.com/janmasrovira/prim-parser, commit 029a4a1, 2026-05-17):
the same three-valued modality (never < possibly < always), re-implemented
here Batteries-only, without the mathlib order/lattice hierarchy.
-/

/-!
# Grip.Modality: the three-valued modality

`never < possibly < always`, the truth values of the grip parser grade algebra.
Batteries-only: no mathlib. Join and meet are the core `Max`/`Min` classes
(`max`/`min`); grip deliberately does not declare `Sup`/`Inf`, so grip-props can import
mathlib (which declares those) without a duplicate-declaration clash.
-/

/-- Three-valued modality tracking whether a property holds always, possibly, or never.
    The order is `never ≤ possibly ≤ always`. -/
inductive Modality where
  | never
  | possibly
  | always
  deriving DecidableEq, Repr

export Modality (never possibly always)

namespace Modality

/-- Supremum on `Modality`: the join in `never < possibly < always`.
    `max a b = a` when `a` is the greater element. -/
def sup : Modality → Modality → Modality
  | always, _      => always
  | _, always      => always
  | possibly, _    => possibly
  | _, possibly    => possibly
  | never, never   => never

/-- Infimum on `Modality`: the meet in `never < possibly < always`. -/
def inf : Modality → Modality → Modality
  | never, _       => never
  | _, never       => never
  | possibly, _    => possibly
  | _, possibly    => possibly
  | always, always => always

-- Join and meet are the core `Max`/`Min` classes; `max`/`min` alias `sup`/`inf`.
instance : Max Modality where max := Modality.sup
instance : Min Modality where min := Modality.inf

/-- Order relation: `never ≤ possibly ≤ always`. -/
def le : Modality → Modality → Prop
  | never, _           => True
  | _, always          => True
  | possibly, possibly => True
  | _, _               => False

instance : LE Modality := ⟨Modality.le⟩
instance : LT Modality := ⟨fun a b => a ≤ b ∧ ¬ b ≤ a⟩

/-- Decidability of `≤` on `Modality`. -/
instance (a b : Modality) : Decidable (a ≤ b) :=
  -- Wildcard arms are expanded to concrete constructors so that `le a b` always
  -- reduces definitionally (a free first argument blocks iota-reduction in Lean).
  match a, b with
  | never,    never    => .isTrue True.intro
  | never,    possibly => .isTrue True.intro
  | never,    always   => .isTrue True.intro
  | possibly, never    => .isFalse id
  | possibly, possibly => .isTrue True.intro
  | possibly, always   => .isTrue True.intro
  | always,   never    => .isFalse id
  | always,   possibly => .isFalse id
  | always,   always   => .isTrue True.intro

/-- Conditional selection driven by `sel : Modality`.
    - `always.ite a b = a` (first branch wins)
    - `never.ite a b = b` (second branch wins)
    - `possibly.ite a b = a` when `a = b`, otherwise `possibly` (conservative) -/
def ite (sel a b : Modality) : Modality :=
  match sel with
  | always   => a
  | never    => b
  | possibly => if a = b then a else possibly

@[simp] theorem ite_always (a b : Modality) : ite always a b = a := rfl
@[simp] theorem ite_never  (a b : Modality) : ite never  a b = b := rfl
@[simp] theorem ite_possibly_eq (a : Modality) : ite possibly a a = a := by
  simp [ite]
@[simp] theorem ite_possibly (a b : Modality) :
    ite possibly a b = if a = b then a else possibly := rfl

/-- `never` is the left identity for join. -/
@[simp] theorem sup_never_left  (a : Modality) : max never a = a := by cases a <;> rfl
/-- `never` is the right identity for join. -/
@[simp] theorem sup_never_right (a : Modality) : max a never = a := by cases a <;> rfl
/-- `always` absorbs on the left for join. -/
@[simp] theorem sup_always_left  (a : Modality) : max always a = always := by cases a <;> rfl
/-- `always` absorbs on the right for join. -/
@[simp] theorem sup_always_right (a : Modality) : max a always = always := by cases a <;> rfl

/-- A join equals `always` iff at least one operand is `always`. -/
@[simp] theorem max_always (a b : Modality) : max a b = always ↔ a = always ∨ b = always := by
  cases a <;> cases b <;> decide

/-- A join equals `never` iff both operands are `never`. -/
@[simp] theorem max_never (a b : Modality) : max a b = never ↔ a = never ∧ b = never := by
  cases a <;> cases b <;> decide

/-- A meet equals `never` iff at least one operand is `never`. -/
@[simp] theorem min_never (a b : Modality) : min a b = never ↔ a = never ∨ b = never := by
  cases a <;> cases b <;> decide

/-- A meet equals `always` iff both operands are `always`. -/
@[simp] theorem min_always (a b : Modality) : min a b = always ↔ a = always ∧ b = always := by
  cases a <;> cases b <;> decide

/-- Join is commutative. -/
theorem sup_comm (a b : Modality) : max a b = max b a := by cases a <;> cases b <;> rfl

/-- If `a ≠ always` then `a ≤ possibly`. -/
theorem le_possibly_of_ne_always {a : Modality} (h : a ≠ always) : a ≤ possibly := by
  cases a
  · exact True.intro
  · exact True.intro
  · exact absurd rfl h

/-- If `a ≠ never` then `possibly ≤ a`. -/
theorem possibly_le_of_ne_never {a : Modality} (h : a ≠ never) : possibly ≤ a := by
  cases a
  · exact absurd rfl h
  · exact True.intro
  · exact True.intro

-- #guard truth-table checks for sup, inf, ite
#guard (Modality.sup never  always   == always)
#guard (Modality.sup always never    == always)
#guard (Modality.sup never  possibly == possibly)
#guard (Modality.sup possibly never  == possibly)
#guard (Modality.sup never  never    == never)
#guard (Modality.sup always always   == always)

#guard (Modality.inf never  always   == never)
#guard (Modality.inf always never    == never)
#guard (Modality.inf always always   == always)
#guard (Modality.inf possibly always == possibly)
#guard (Modality.inf always possibly == possibly)
#guard (Modality.inf never  never    == never)
#guard (Modality.inf possibly possibly == possibly)

#guard (Modality.ite always never  always == never)
#guard (Modality.ite never  never  always == always)
#guard (Modality.ite possibly never  always  == possibly)
#guard (Modality.ite possibly never  never   == never)
#guard (Modality.ite possibly always always  == always)
#guard (Modality.ite possibly possibly possibly == possibly)

end Modality
