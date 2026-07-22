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

private theorem toDigitsCore_head_nonzero :
    ∀ (fuel n : Nat) (_hn : 0 < n), 0 < fuel → n < 10 ^ fuel →
      ∃ c rest, Nat.toDigitsCore 10 fuel n [] = c :: rest ∧ 49 ≤ c.toNat ∧ c.toNat ≤ 57 := by
  intro fuel
  induction fuel with
  | zero => intro n hn hf; omega
  | succ f ih =>
    intro n hn _ hb
    -- Expand the definition of toDigitsCore once.
    have core_eq : Nat.toDigitsCore 10 (f + 1) n [] =
        if n / 10 = 0 then [Nat.digitChar (n % 10)]
        else Nat.toDigitsCore 10 f (n / 10) [Nat.digitChar (n % 10)] := rfl
    by_cases h10 : n / 10 = 0
    · -- n < 10, n > 0: single digit n ∈ [1,9]
      have hn10 : n < 10 := by omega
      have h49 : 49 ≤ (Nat.digitChar (n % 10)).toNat := by
        have : n % 10 = n := Nat.mod_eq_of_lt hn10
        rw [this]; interval_cases n <;> decide
      have h57 : (Nat.digitChar (n % 10)).toNat ≤ 57 :=
        (digitChar_bound (n % 10) (Nat.mod_lt _ (by omega))).2
      exact ⟨Nat.digitChar (n % 10), [], by rw [core_eq, if_pos h10], h49, h57⟩
    · -- n ≥ 10: head comes from recursive call on n/10
      have hqpos : 0 < n / 10 := Nat.div_pos (by omega) (by omega)
      have hfuel : 0 < f := by
        rcases Nat.eq_zero_or_pos f with rfl | hfp
        · norm_num at hb
          exact absurd (Nat.div_eq_of_lt hb) h10
        · exact hfp
      have hbound : n / 10 < 10 ^ f := by
        apply Nat.div_lt_of_lt_mul
        have : 10 ^ (f + 1) = 10 * 10 ^ f := by ring
        linarith
      obtain ⟨c, rest, hceq, h49, h57⟩ := ih (n / 10) hqpos hfuel hbound
      refine ⟨c, rest ++ [Nat.digitChar (n % 10)], ?_, h49, h57⟩
      rw [core_eq, if_neg h10, toDigitsCore_append f (n / 10) [Nat.digitChar (n % 10)], hceq]
      simp [List.cons_append]

/-- For a positive natural, the most-significant decimal digit is in 1-9.
This means `Ascii.isDigit19` of its byte holds in the rendered string. -/
theorem toDigits_head_pos (n : Nat) (hn : 0 < n) :
    49 ≤ (Nat.toDigits 10 n).head!.toNat ∧ (Nat.toDigits 10 n).head!.toNat ≤ 57 := by
  rw [Nat.toDigits]
  obtain ⟨c, rest, hceq, h49, h57⟩ := toDigitsCore_head_nonzero (n + 1) n hn (by omega) (by
    calc n < n + 1 := by omega
      _ ≤ 10 ^ (n + 1) := Nat.le_of_lt (Nat.lt_pow_self (by omega)))
  rw [hceq]
  simp [h49, h57]

theorem toDigits_nonempty (n : Nat) (hn : 0 < n) : Nat.toDigits 10 n ≠ [] := fun h => by
  have := (toDigits_head_pos n hn).2; rw [h] at this; exact absurd this (by decide)

end GripProps.NatDigits
