/-
Copyright (c) 2026 Jonathan Cubides. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Cubides

Adapted from PrimParser/Basic.lean in prim-parser by Jan Mas Rovira
(https://github.com/janmasrovira/prim-parser, commit 5a5ff0d, 2026-05-31):
the error/consumption Grade, its named grades, the choice/ite rule and
consumptionWitness, re-implemented here over grip's Batteries-only Modality.
-/

import Grip.Modality

/-!
# Grade

Parser grade algebra for grip: `structure Grade` (tracking error and consumption
`Modality`), the named grades, `Grade.mul`/`Grade.choice`, and
`consumptionWitness` with its composition lemmas.

No mathlib. `Monoid`/`Lattice` instances for `Grade` belong in grip-props.
-/

open Modality

/-- A parser's static grade: whether it may/must produce errors and
    whether it may/must consume input. -/
structure Grade where
  /-- Whether the parser may/must error: `never`, `possibly`, or `always`. -/
  errors   : Modality
  /-- Whether the parser may/must consume input: `never`, `possibly`, or `always`. -/
  consumes : Modality
  deriving DecidableEq, Repr

namespace Grade

-- Named grades ----------------------------------------------------------

/-- A parser that always consumes and possibly errors. -/
abbrev conditional : Grade where
  consumes := always
  errors   := possibly

/-- A parser that possibly consumes and never errors. -/
abbrev flexible : Grade where
  consumes := possibly
  errors   := never

/-- A parser that possibly consumes and possibly errors. -/
abbrev fallible : Grade where
  consumes := possibly
  errors   := possibly

/-- A parser that never consumes and never errors. -/
abbrev pure : Grade where
  consumes := never
  errors   := never

/-- A parser that never consumes and possibly errors. -/
abbrev lookahead : Grade where
  consumes := never
  errors   := possibly

/-- A parser that never consumes and always errors. -/
abbrev empty : Grade where
  consumes := never
  errors   := always

/-- The impossible grade: always consumes, never errors.
    No parser can inhabit this grade on arbitrary input (it must accept empty input). -/
abbrev impossible : Grade where
  consumes := always
  errors   := never

-- Multiplication (sequential composition) --------------------------------

/-- Sequential composition: the grade of `p >>= q` is `mul g1 g2`,
    with errors and consumption each being the join of the two grades. -/
def mul (a b : Grade) : Grade :=
  ⟨max a.errors b.errors, max a.consumes b.consumes⟩

/-- The identity grade for sequential composition: `⟨never, never⟩ = pure`. -/
def one : Grade := ⟨never, never⟩

instance : Mul Grade := ⟨Grade.mul⟩
instance : One Grade := ⟨Grade.one⟩

-- Alternative (ordered choice) -------------------------------------------

/-- Ordered-choice grade: errors is the meet (both must agree to fail),
    consumption is `a.errors.ite b.consumes a.consumes`
    (if `a` always errors, use `b`'s consumption; if `a` never errors, use `a`'s). -/
def choice (a b : Grade) : Grade where
  errors   := min a.errors b.errors
  consumes := a.errors.ite b.consumes a.consumes

-- Lemmas needed by the byte-parser proofs --------------------------------

/-- The error grade of a product is the join of the error grades. -/
theorem grade_mul_errors (a b : Grade) : (a * b).errors = max a.errors b.errors := by
  cases a; cases b; rfl

/-- The consumption grade of a product is the join of the consumption grades. -/
theorem grade_mul_consumes (a b : Grade) : (a * b).consumes = max a.consumes b.consumes := by
  cases a; cases b; rfl

-- Guard checks -----------------------------------------------------------
#guard (Grade.mul fallible fallible == fallible)
#guard (Grade.choice fallible fallible == fallible)
#guard (Grade.mul pure fallible == fallible)
#guard (Grade.mul fallible pure == fallible)

end Grade

export Grade (conditional flexible fallible pure lookahead empty impossible)

-- Consumption witness ----------------------------------------------------

/-- Relates remaining size `n` and result size `m` according to a `Modality` grade:
    - `always`   requires strict decrease (`n < m`, i.e. at least one token consumed)
    - `possibly`  allows `≤` (consumed some or none)
    - `never`    requires equality (no input consumed) -/
abbrev consumptionWitness (n m : Nat) : Modality → Prop
  | always   => n < m
  | possibly => n ≤ m
  | never    => n = m

namespace consumptionWitness

/-- A reflexive witness holds for any grade `a ≤ possibly`
    (i.e. `a ≠ always`), since no input has been consumed. -/
@[simp] theorem rfl {n : Nat} {a : Modality} (h : a ≤ possibly) :
    consumptionWitness n n a := by
  cases a
  · -- never: n = n
    rfl
  · -- possibly: n ≤ n
    exact Nat.le_refl n
  · -- always: always ≤ possibly is False
    exact absurd h (by decide)

/-- Transitivity: chain two witnesses through a common midpoint.
    If `gc` witnesses `(n2, n1)` and `gc'` witnesses `(n3, n2)`,
    then `max gc gc'` witnesses `(n3, n1)`. -/
theorem trans {gc gc' : Modality} {n1 n2 n3 : Nat}
    (w1 : consumptionWitness n2 n1 gc)
    (w2 : consumptionWitness n3 n2 gc')
    : consumptionWitness n3 n1 (max gc gc') := by
  -- Bridge `max` to `Modality.sup` (the `Max` instance body), then unfold
  -- `sup` using equation lemmas after making both grade arguments concrete.
  have max_sup : ∀ a b : Modality, max a b = Modality.sup a b := by intros; rfl
  cases gc <;> cases gc' <;>
    simp only [consumptionWitness, max_sup, Modality.sup] at * <;>
    omega

/-- If the error grade `ge'` is at most `possibly` (i.e. `ge' ≠ always`),
    a consumption witness for the second branch `gc'` lifts to a witness for
    the `ite`-computed consumption `ge'.ite gc gc'`. -/
theorem ite_left {ge' gc gc' : Modality} {n m : Nat}
    (c : ge' ≤ possibly)
    (w : consumptionWitness n m gc')
    : consumptionWitness n m (ge'.ite gc gc') := by
  -- After full case-split, `simp_all` reduces `Modality.ite` and
  -- `consumptionWitness` to arithmetic goals; `omega` closes the rest.
  cases ge' <;> cases gc <;> cases gc' <;>
    first | exact absurd c (by decide)
          | (simp_all [Modality.ite, consumptionWitness]; try omega)

/-- If the error grade `ge'` is at least `possibly` (i.e. `ge' ≠ never`),
    a consumption witness for the first branch `gc` lifts to a witness for
    the `ite`-computed consumption `ge'.ite gc gc'`. -/
theorem ite_right {ge' gc gc' : Modality} {n m : Nat}
    (c : possibly ≤ ge')
    (w : consumptionWitness n m gc)
    : consumptionWitness n m (ge'.ite gc gc') := by
  cases ge' <;> cases gc <;> cases gc' <;>
    first | exact absurd c (by decide)
          | (simp_all [Modality.ite, consumptionWitness]; try omega)

end consumptionWitness
