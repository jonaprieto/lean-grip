/-
Copyright (c) 2026 Jonathan Cubides. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Cubides
-/
import Mathlib
import Grip.Json
import GripProps.Json.Bytes
import GripProps.Json.NatDigits

/-!
# JSON number round-trip (integers)

`decodeNumberBytes?` over `(renderNum m 0).toUTF8` recovers `num m 0`. Glues the ByteArray/toUTF8
fold bridge and the decimal-digit fold inversion through `numByte`'s state machine on the
digit bytes rendered for an integer.
-/

set_option maxHeartbeats 1000000

open Grip.Json Grip.Json.Decode Grip.Json.Json

namespace GripProps.Number

/-- A decimal digit character's byte is none of the structural bytes `numByte` special-cases, so
`numByte` takes the digit branch and, in phase 0, folds it into the mantissa. -/
theorem foldl_numByte_digits (ds : List Char) (st : NState) (hp : st.phase = 0)
    (hd : ∀ c ∈ ds, 48 ≤ c.toNat ∧ c.toNat ≤ 57) :
    ds.foldl (fun s c => numByte s (UInt8.ofNat c.toNat)) st
      = { st with mant := ds.foldl (fun a c => a * 10 + (c.toNat - 48)) st.mant } := by
  induction ds generalizing st with
  | nil => simp
  | cons c cs ih =>
    obtain ⟨hc1, hc2⟩ := hd c (by simp)
    have hsize : UInt8.size = 256 := by decide
    have hb : (UInt8.ofNat c.toNat).toNat = c.toNat := UInt8.toNat_ofNat_of_lt' (by omega)
    have h48 : ((48 : UInt8)).toNat = 48 := by decide
    have key : ∀ k : Nat, k < 256 → k ≠ c.toNat →
        (UInt8.ofNat c.toNat == UInt8.ofNat k) = false := by
      intro k hk256 hk
      rw [beq_eq_false_iff_ne, ne_eq]
      intro h
      have hkb : (UInt8.ofNat k).toNat = k := UInt8.toNat_ofNat_of_lt' (by omega)
      have := congrArg UInt8.toNat h
      rw [hb, hkb] at this
      exact hk this.symm
    have hle : (48 : UInt8) ≤ UInt8.ofNat c.toNat := by
      rw [UInt8.le_iff_toNat_le, hb, h48]; omega
    have hd48 : (UInt8.ofNat c.toNat - 48).toNat = c.toNat - 48 := by
      rw [UInt8.toNat_sub_of_le _ _ hle, hb, h48]
    have hstep : numByte st (UInt8.ofNat c.toNat)
        = { st with mant := st.mant * 10 + (c.toNat - 48) } := by
      simp only [numByte, show (46 : UInt8) = UInt8.ofNat 46 from rfl,
        show (101 : UInt8) = UInt8.ofNat 101 from rfl, show (69 : UInt8) = UInt8.ofNat 69 from rfl,
        show (43 : UInt8) = UInt8.ofNat 43 from rfl, show (45 : UInt8) = UInt8.ofNat 45 from rfl,
        key 46 (by omega) (by omega), key 101 (by omega) (by omega), key 69 (by omega) (by omega),
        key 43 (by omega) (by omega), key 45 (by omega) (by omega)]
      simp [Bool.or_self, hp, hd48]
    rw [List.foldl_cons, List.foldl_cons, hstep]
    rw [ih _ (by simp [hp]) (fun c hc => hd c (by simp [hc]))]
