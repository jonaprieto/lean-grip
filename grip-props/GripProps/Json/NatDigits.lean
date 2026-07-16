/-
Copyright (c) 2026 Jonathan Cubides. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Cubides
-/
import Mathlib

/-!
# Decimal-digit fold inversion

`Nat.repr` / `Nat.toDigits` render a number as its decimal digit characters (most significant
first). This file proves the Horner fold `a ↦ a*10 + (c - '0')` over those digits recovers the
number — the arithmetic core of the JSON number round-trip, with no library support in 4.28.
-/

set_option maxHeartbeats 1000000

namespace GripProps.NatDigits

/-- The Horner step the JSON number decoder uses on a decimal digit character. -/
def H (a : Nat) (c : Char) : Nat := a * 10 + (c.toNat - 48)

/-- `toDigitsCore` prepends the digits of `n` to its accumulator. -/
theorem toDigitsCore_append :
    ∀ (fuel n : Nat) (ds : List Char),
      Nat.toDigitsCore 10 fuel n ds = Nat.toDigitsCore 10 fuel n [] ++ ds := by
  intro fuel
  induction fuel with
  | zero => intro n ds; rfl
  | succ f ih =>
    intro n ds
    unfold Nat.toDigitsCore
    by_cases h : n / 10 = 0
    · simp [h]
    · simp only [h, if_false]
      rw [ih (n / 10) (Nat.digitChar (n % 10) :: ds), ih (n / 10) [Nat.digitChar (n % 10)]]
      simp

/-- `Nat.digitChar` of a decimal digit lands on `'0'..'9'`, so subtracting `'0'` inverts it. -/
theorem digitChar_toNat_sub (d : Nat) (hd : d < 10) : (Nat.digitChar d).toNat - 48 = d := by
  interval_cases d <;> decide

/-- The Horner fold over `n`'s decimal digits recovers `n`. -/
theorem foldl_toDigitsCore (n : Nat) :
    ∀ (fuel : Nat), 0 < fuel → n < 10 ^ fuel →
      (Nat.toDigitsCore 10 fuel n []).foldl H 0 = n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro fuel hf hn
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    have hpow : (10 : Nat) ^ (f + 1) = 10 * 10 ^ f := by rw [pow_succ]; ring
    show (if n / 10 = 0 then [Nat.digitChar (n % 10)]
          else Nat.toDigitsCore 10 f (n / 10) [Nat.digitChar (n % 10)]).foldl H 0 = n
    split
    · rename_i h
      have hlt : n < 10 := by omega
      simp only [List.foldl_cons, List.foldl_nil, H, Nat.zero_mul, Nat.zero_add,
        Nat.mod_eq_of_lt hlt]
      exact digitChar_toNat_sub n hlt
    · rename_i h
      have hdlt : n / 10 < n := Nat.div_lt_self (by omega) (by omega)
      have hfpos : 0 < f := by
        rcases Nat.eq_zero_or_pos f with hf0 | hf0
        · exfalso; subst hf0; rw [zero_add, pow_one] at hn; omega
        · exact hf0
      rw [toDigitsCore_append, List.foldl_append,
        ih (n / 10) hdlt f hfpos (by omega)]
      simp only [List.foldl_cons, List.foldl_nil, H,
        digitChar_toNat_sub (n % 10) (Nat.mod_lt _ (by omega))]
      omega

/-- `Nat.digitChar` of a decimal digit is an ASCII digit byte. -/
theorem digitChar_bound (d : Nat) (hd : d < 10) :
    48 ≤ (Nat.digitChar d).toNat ∧ (Nat.digitChar d).toNat ≤ 57 := by
  interval_cases d <;> decide

/-- Every character of `Nat.toDigits 10 k` is a decimal digit. -/
theorem mem_toDigits_bound (k : Nat) :
    ∀ c ∈ Nat.toDigits 10 k, 48 ≤ c.toNat ∧ c.toNat ≤ 57 := by
  have core : ∀ (fuel n : Nat) (ds : List Char),
      (∀ c ∈ ds, 48 ≤ c.toNat ∧ c.toNat ≤ 57) →
      ∀ c ∈ Nat.toDigitsCore 10 fuel n ds, 48 ≤ c.toNat ∧ c.toNat ≤ 57 := by
    intro fuel
    induction fuel with
    | zero => intro n ds hds c hc; exact hds c hc
    | succ f ih =>
      intro n ds hds c hc
      have hdig := digitChar_bound (n % 10) (Nat.mod_lt _ (by omega))
      rw [show Nat.toDigitsCore 10 (f + 1) n ds
            = (if n / 10 = 0 then Nat.digitChar (n % 10) :: ds
               else Nat.toDigitsCore 10 f (n / 10) (Nat.digitChar (n % 10) :: ds)) from rfl] at hc
      split at hc
      · rcases List.mem_cons.mp hc with rfl | hc'
        · exact hdig
        · exact hds c hc'
      · exact ih (n / 10) _ (fun c' hc'' => by
          rcases List.mem_cons.mp hc'' with rfl | h
          · exact hdig
          · exact hds c' h) c hc
  exact core (k + 1) k [] (by simp)

/-- **Decimal fold inversion.** Folding the Horner step over `Nat.repr n`'s characters gives `n`. -/
theorem foldl_repr (n : Nat) : (Nat.repr n).toList.foldl H 0 = n := by
  rw [Nat.repr, String.toList_ofList, Nat.toDigits]
  exact foldl_toDigitsCore n (n + 1) (by omega) (by
    calc n < n + 1 := by omega
      _ ≤ 10 ^ (n + 1) := Nat.le_of_lt (Nat.lt_pow_self (by omega)))

end GripProps.NatDigits
