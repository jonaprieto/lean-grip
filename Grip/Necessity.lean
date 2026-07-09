/-
Copyright (c) 2026 Jonathan Cubides. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Cubides
-/

/-!
# Necessity

Three-valued modality `never < possibly < always` for the grip parser grade algebra.
Batteries-only: no mathlib. Join and meet are the core `Max`/`Min` classes
(`max`/`min`); grip deliberately does not declare `Sup`/`Inf`, so grip-props can import
mathlib (which declares those) without a duplicate-declaration clash.
-/

/-- Three-valued modality tracking whether a property holds always, possibly, or never.
    The order is `never ≤ possibly ≤ always`. -/
inductive Necessity where
  | never
  | possibly
  | always
  deriving DecidableEq, Repr

export Necessity (never possibly always)

namespace Necessity

/-- Supremum on `Necessity`: the join in `never < possibly < always`.
    `max a b = a` when `a` is the greater element. -/
def sup : Necessity → Necessity → Necessity
  | always, _      => always
  | _, always      => always
  | possibly, _    => possibly
  | _, possibly    => possibly
  | never, never   => never

/-- Infimum on `Necessity`: the meet in `never < possibly < always`. -/
def inf : Necessity → Necessity → Necessity
  | never, _       => never
  | _, never       => never
  | possibly, _    => possibly
  | _, possibly    => possibly
  | always, always => always

-- Join and meet are the core `Max`/`Min` classes; `max`/`min` alias `sup`/`inf`.
instance : Max Necessity where max := Necessity.sup
instance : Min Necessity where min := Necessity.inf

/-- Order relation: `never ≤ possibly ≤ always`. -/
def le : Necessity → Necessity → Prop
  | never, _           => True
  | _, always          => True
  | possibly, possibly => True
  | _, _               => False

instance : LE Necessity := ⟨Necessity.le⟩
instance : LT Necessity := ⟨fun a b => a ≤ b ∧ ¬ b ≤ a⟩

/-- Decidability of `≤` on `Necessity`. -/
instance (a b : Necessity) : Decidable (a ≤ b) :=
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

/-- Conditional selection driven by `sel : Necessity`.
    - `always.ite a b = a` (first branch wins)
    - `never.ite a b = b` (second branch wins)
    - `possibly.ite a b = a` when `a = b`, otherwise `possibly` (conservative) -/
def ite (sel a b : Necessity) : Necessity :=
  match sel with
  | always   => a
  | never    => b
  | possibly => if a = b then a else possibly

@[simp] theorem ite_always (a b : Necessity) : ite always a b = a := rfl
@[simp] theorem ite_never  (a b : Necessity) : ite never  a b = b := rfl
@[simp] theorem ite_possibly_eq (a : Necessity) : ite possibly a a = a := by
  simp [ite]
@[simp] theorem ite_possibly (a b : Necessity) :
    ite possibly a b = if a = b then a else possibly := rfl

/-- `never` is the left identity for join. -/
@[simp] theorem sup_never_left  (a : Necessity) : max never a = a := by cases a <;> rfl
/-- `never` is the right identity for join. -/
@[simp] theorem sup_never_right (a : Necessity) : max a never = a := by cases a <;> rfl
/-- `always` absorbs on the left for join. -/
@[simp] theorem sup_always_left  (a : Necessity) : max always a = always := by cases a <;> rfl
/-- `always` absorbs on the right for join. -/
@[simp] theorem sup_always_right (a : Necessity) : max a always = always := by cases a <;> rfl
/-- `possibly` absorbs `never` on the left for join. -/
@[simp] theorem sup_possibly_left : max possibly never = possibly := rfl
/-- `possibly` absorbs `never` on the right for join. -/
@[simp] theorem sup_possibly_right : max never possibly = possibly := rfl

/-- A join equals `always` iff at least one operand is `always`. -/
@[simp] theorem max_always (a b : Necessity) : max a b = always ↔ a = always ∨ b = always := by
  cases a <;> cases b <;> decide

/-- A join equals `never` iff both operands are `never`. -/
@[simp] theorem max_never (a b : Necessity) : max a b = never ↔ a = never ∧ b = never := by
  cases a <;> cases b <;> decide

/-- A meet equals `never` iff at least one operand is `never`. -/
@[simp] theorem min_never (a b : Necessity) : min a b = never ↔ a = never ∨ b = never := by
  cases a <;> cases b <;> decide

/-- A meet equals `always` iff both operands are `always`. -/
@[simp] theorem min_always (a b : Necessity) : min a b = always ↔ a = always ∧ b = always := by
  cases a <;> cases b <;> decide

/-- Join is commutative. -/
theorem sup_comm (a b : Necessity) : max a b = max b a := by cases a <;> cases b <;> rfl

/-- If `a ≠ always` then `a ≤ possibly`. -/
theorem le_possibly_of_ne_always {a : Necessity} (h : a ≠ always) : a ≤ possibly := by
  cases a
  · exact True.intro
  · exact True.intro
  · exact absurd rfl h

/-- If `a ≠ never` then `possibly ≤ a`. -/
theorem possibly_le_of_ne_never {a : Necessity} (h : a ≠ never) : possibly ≤ a := by
  cases a
  · exact absurd rfl h
  · exact True.intro
  · exact True.intro

-- #guard truth-table checks for sup, inf, ite
#guard (Necessity.sup never  always   == always)
#guard (Necessity.sup always never    == always)
#guard (Necessity.sup never  possibly == possibly)
#guard (Necessity.sup possibly never  == possibly)
#guard (Necessity.sup never  never    == never)
#guard (Necessity.sup always always   == always)

#guard (Necessity.inf never  always   == never)
#guard (Necessity.inf always never    == never)
#guard (Necessity.inf always always   == always)
#guard (Necessity.inf possibly always == possibly)
#guard (Necessity.inf always possibly == possibly)
#guard (Necessity.inf never  never    == never)
#guard (Necessity.inf possibly possibly == possibly)

#guard (Necessity.ite always never  always == never)
#guard (Necessity.ite never  never  always == always)
#guard (Necessity.ite possibly never  always  == possibly)
#guard (Necessity.ite possibly never  never   == never)
#guard (Necessity.ite possibly always always  == always)
#guard (Necessity.ite possibly possibly possibly == possibly)

end Necessity
