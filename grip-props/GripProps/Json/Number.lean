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

/-- An ASCII character encodes to a single byte, its code point. -/
theorem ascii_encode (c : Char) (h : c.toNat ≤ 127) :
    String.utf8EncodeChar c = [UInt8.ofNat c.toNat] := by
  have hval : c.val ≤ 127 := by rw [UInt32.le_iff_toNat_le]; exact h
  have hbyte : c.val.toUInt8 = UInt8.ofNat c.toNat := by
    rw [Char.toNat]; exact UInt8.toNat_inj.mp rfl
  rw [String.utf8EncodeChar_eq_singleton (Char.utf8Size_eq_one_iff.mpr hval), hbyte]

/-- Over ASCII characters, `flatMap`-encoding is `map`ping each to its byte. -/
theorem flatMap_ascii (cs : List Char) (h : ∀ c ∈ cs, c.toNat ≤ 127) :
    cs.flatMap String.utf8EncodeChar = cs.map (fun c => UInt8.ofNat c.toNat) := by
  induction cs with
  | nil => simp
  | cons c cs ih =>
    rw [List.flatMap_cons, List.map_cons, ascii_encode c (h c (by simp)),
      ih (fun c hc => h c (by simp [hc]))]
    simp

/-- Single `numByte` step on a decimal digit, phase 0 or 1: accumulate the mantissa (and, in
phase 1, count a fractional digit); other fields unchanged. -/
theorem numByte_digit (st : NState) (c : Char) (hc1 : 48 ≤ c.toNat) (hc2 : c.toNat ≤ 57) :
    numByte st (UInt8.ofNat c.toNat) =
      (if st.phase = 1 then
        { st with mant := st.mant * 10 + (c.toNat - 48), fracLen := st.fracLen + 1 }
       else if st.phase = 0 then { st with mant := st.mant * 10 + (c.toNat - 48) }
       else { st with expVal := st.expVal * 10 + (c.toNat - 48) }) := by
  have hsize : UInt8.size = 256 := by decide
  have hb : (UInt8.ofNat c.toNat).toNat = c.toNat := UInt8.toNat_ofNat_of_lt' (by omega)
  have h48 : ((48 : UInt8)).toNat = 48 := by decide
  have key : ∀ k : Nat, k < 256 → k ≠ c.toNat →
      (UInt8.ofNat c.toNat == UInt8.ofNat k) = false := by
    intro k hk256 hk
    rw [beq_eq_false_iff_ne, ne_eq]; intro h
    have hkb : (UInt8.ofNat k).toNat = k := UInt8.toNat_ofNat_of_lt' (by omega)
    have := congrArg UInt8.toNat h; rw [hb, hkb] at this; exact hk this.symm
  have hle : (48 : UInt8) ≤ UInt8.ofNat c.toNat := by
    rw [UInt8.le_iff_toNat_le, hb, h48]; omega
  have hd48 : (UInt8.ofNat c.toNat - 48).toNat = c.toNat - 48 := by
    rw [UInt8.toNat_sub_of_le _ _ hle, hb, h48]
  simp only [numByte, show (46 : UInt8) = UInt8.ofNat 46 from rfl,
    show (101 : UInt8) = UInt8.ofNat 101 from rfl, show (69 : UInt8) = UInt8.ofNat 69 from rfl,
    show (43 : UInt8) = UInt8.ofNat 43 from rfl, show (45 : UInt8) = UInt8.ofNat 45 from rfl,
    key 46 (by omega) (by omega), key 101 (by omega) (by omega), key 69 (by omega) (by omega),
    key 43 (by omega) (by omega), key 45 (by omega) (by omega)]
  simp only [Bool.or_self, hd48]
  rcases Nat.lt_trichotomy st.phase 1 with h | h | h
  · have : st.phase = 0 := by omega
    simp [this]
  · simp [h]
  · simp [show ¬ st.phase = 0 from by omega, show ¬ st.phase = 1 from by omega]

/-- Phase-1 (fractional) `numByte` fold: accumulate the mantissa and count each digit. -/
theorem foldl_numByte_frac (ds : List Char) (st : NState) (hp : st.phase = 1)
    (hd : ∀ c ∈ ds, 48 ≤ c.toNat ∧ c.toNat ≤ 57) :
    ds.foldl (fun s c => numByte s (UInt8.ofNat c.toNat)) st
      = { st with mant := ds.foldl (fun a c => a * 10 + (c.toNat - 48)) st.mant,
                  fracLen := st.fracLen + ds.length } := by
  induction ds generalizing st with
  | nil => simp
  | cons c cs ih =>
    obtain ⟨hc1, hc2⟩ := hd c (by simp)
    rw [List.foldl_cons, numByte_digit st c hc1 hc2, if_pos hp,
      ih _ (by simp [hp]) (fun c hc => hd c (by simp [hc]))]
    simp [List.foldl_cons, hp, Nat.add_assoc, Nat.add_comm 1]

/-- Folding `numByte` over an ASCII digit string's UTF-8 bytes accumulates the mantissa. -/
theorem foldl_numByte_ascii (cs : List Char) (st : NState) (hp : st.phase = 0)
    (hd : ∀ c ∈ cs, 48 ≤ c.toNat ∧ c.toNat ≤ 57) :
    (cs.flatMap String.utf8EncodeChar).foldl numByte st
      = { st with mant := cs.foldl (fun a c => a * 10 + (c.toNat - 48)) st.mant } := by
  rw [flatMap_ascii cs (fun c hc => by have := hd c hc; omega), List.foldl_map]
  exact foldl_numByte_digits cs st hp hd

/-- Phase-1 byte-form fold: over an ASCII digit string's UTF-8 bytes, accumulate mantissa and
count fractional digits. -/
theorem foldl_numByte_frac_ascii (cs : List Char) (st : NState) (hp : st.phase = 1)
    (hd : ∀ c ∈ cs, 48 ≤ c.toNat ∧ c.toNat ≤ 57) :
    (cs.flatMap String.utf8EncodeChar).foldl numByte st
      = { st with mant := cs.foldl (fun a c => a * 10 + (c.toNat - 48)) st.mant,
                  fracLen := st.fracLen + cs.length } := by
  rw [flatMap_ascii cs (fun c hc => by have := hd c hc; omega), List.foldl_map]
  exact foldl_numByte_frac cs st hp hd

/-- The decimal-point byte switches the decoder to the fractional phase. -/
theorem numByte_dot (st : NState) : numByte st (UInt8.ofNat ('.').toNat) = { st with phase := 1 } :=
  rfl

/-- The Horner fold over leading zeros starting from `0` stays `0`. -/
theorem foldl_H_zeros (n : Nat) :
    (List.replicate n '0').foldl (fun a c => a * 10 + (c.toNat - 48)) 0 = 0 := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.replicate_succ, List.foldl_cons]; norm_num; exact ih

/-- The `numByte` fold over an integer part, the point, and a fractional part yields the mantissa
of all digits together and a fractional length equal to the fractional part. -/
theorem fold_frac_chars (intg fracg : List Char)
    (hi : ∀ c ∈ intg, 48 ≤ c.toNat ∧ c.toNat ≤ 57)
    (hf : ∀ c ∈ fracg, 48 ≤ c.toNat ∧ c.toNat ≤ 57) :
    (intg.flatMap String.utf8EncodeChar ++ String.utf8EncodeChar '.'
        ++ fracg.flatMap String.utf8EncodeChar).foldl numByte {}
      = { mant := (intg ++ fracg).foldl (fun a c => a * 10 + (c.toNat - 48)) 0,
          fracLen := fracg.length, phase := 1 } := by
  rw [List.append_assoc, List.foldl_append, foldl_numByte_ascii _ _ rfl hi,
    ascii_encode '.' (by decide), List.foldl_append, List.foldl_cons, List.foldl_nil,
    numByte_dot, foldl_numByte_frac_ascii _ _ rfl hf]
  simp [List.foldl_append]

/-- **Integer number round-trip.** For a nonnegative integer, decoding the bytes of its rendering
recovers it. Composes the ByteArray/toUTF8 fold bridge, the digit-fold inversion, and the numByte
accumulation. -/
theorem decode_renderNum_int (m : Int) (hm : 0 ≤ m) :
    decodeNumberBytes? (renderNum m 0).toUTF8 0 (renderNum m 0).toUTF8.size
      = some (Json.num m 0) := by
  have hrepr : renderNum m 0 = Nat.repr m.toNat := by
    have h1 : renderNum m 0 = toString m := by unfold renderNum; simp
    have h2 : toString m = toString ((m.toNat : Int)) := by rw [Int.toNat_of_nonneg hm]
    rw [h1, h2]; exact String.toByteArray_inj.mp rfl
  have hchars : (renderNum m 0).toList = Nat.toDigits 10 m.toNat := by
    rw [hrepr, Nat.repr, String.toList_ofList]
  have hst : (renderNum m 0).toUTF8.foldl numByte {} 0 (renderNum m 0).toUTF8.size
      = ({ mant := m.toNat } : NState) := by
    rw [GripProps.Bytes.toUTF8_foldl, hchars,
      foldl_numByte_ascii _ _ rfl (GripProps.NatDigits.mem_toDigits_bound m.toNat)]
    have hfold : (Nat.toDigits 10 m.toNat).foldl (fun a c => a * 10 + (c.toNat - 48)) 0
        = m.toNat := by
      have := GripProps.NatDigits.foldl_repr m.toNat
      rw [Nat.repr, String.toList_ofList] at this
      exact this
    simp only [hfold]
  unfold decodeNumberBytes?
  rw [hst]
  simp [Int.toNat_of_nonneg hm, maxExp]
