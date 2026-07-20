/-
Copyright (c) 2026 Jonathan Cubides. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Cubides
-/
import Mathlib
import Grip.Json
import GripProps.Json.Bytes
import GripProps.Json.Leaf

/-!
# `scanStr` walk denotation

`scanStr` scans a JSON string body byte-by-byte until the closing quote, validating `\`-escapes
via `escEnd` and accumulating whether any escape occurred. This file gives its step lemmas (one
normal byte, one escape, the closing quote) and, on top of them, the walk over a rendered body
`(escape s).toUTF8`, culminating in `scanStr` returning `s` — the string leaf of the JSON
round-trip.
-/

set_option maxHeartbeats 1000000

open Grip.Json Grip.Json.Decode Grip.Json.Json

namespace GripProps.ScanStr

/-- Inverting `escapeChar c = [c]`: the character fell through every escape branch, so it is
`≥ 0x20` and neither `"` nor `\`. -/
theorem passthrough_props (c : Char) (h : escapeChar c = [c]) :
    32 ≤ c.toNat ∧ c.val ≠ 34 ∧ c.val ≠ 92 := by
  unfold escapeChar at h
  by_cases h34 : c = '"'
  · simp [h34] at h
  by_cases h92 : c = '\\'
  · simp [h92] at h
  by_cases hn : c = '\n'
  · simp [hn] at h
  by_cases ht : c = '\t'
  · simp [ht] at h
  by_cases hr : c = '\r'
  · simp [hr] at h
  by_cases hb8 : c = Char.ofNat 8
  · simp [hb8] at h
  by_cases hf12 : c = Char.ofNat 12
  · simp [hf12] at h
  by_cases hctrl : c.toNat < 0x20
  · simp [h34, h92, hn, ht, hr, hb8, hf12, hctrl] at h
  refine ⟨by omega, ?_, ?_⟩
  · intro he; exact h34 (Char.eq_of_val_eq (he.trans (by decide)))
  · intro he; exact h92 (Char.eq_of_val_eq (he.trans (by decide)))

/-- Decoding the UTF-8 bytes of a string recovers it: `fromUTF8!` inverts `toUTF8`. The body that
`scanStr` extracts at the closing quote is exactly `(escape s).toUTF8`, so this turns it back into
`escape s`. -/
theorem fromUTF8!_toUTF8 (s : String) : String.fromUTF8! s.toUTF8 = s := by
  have hv : s.toUTF8.IsValidUTF8 := by
    rw [show s.toUTF8 = s.toList.utf8Encode from by
      rw [String.toUTF8_eq_toByteArray, ← String.utf8Encode_toList]]
    exact ByteArray.isValidUTF8_utf8Encode
  unfold String.fromUTF8!
  rw [dif_pos hv]
  apply String.toByteArray_inj.mp
  exact ByteArray.ext rfl

/-- Every UTF-8 byte of a passthrough character (`≥ 0x20`, not `"` or `\`) is scan-normal: it is
not the closing quote, not a backslash, and not a control byte. Single-byte chars carry their
codepoint (in `[0x20, 0x7F] \ {34, 92}`); every byte of a multi-byte char has its high bit set
(`≥ 0x80`), so all bounds hold. This lets `scanStr` walk a passthrough char's bytes one by one. -/
theorem passthrough_bytes_normal (c : Char) (h32 : 32 ≤ c.toNat) (hq : c.val ≠ 34)
    (hbs : c.val ≠ 92) (b : UInt8) (hb : b ∈ String.utf8EncodeChar c) :
    b ≠ 34 ∧ b ≠ 92 ∧ ¬ b < 32 := by
  have hpos := Char.utf8Size_pos c
  have hle4 := Char.utf8Size_le_four c
  rcases (show c.utf8Size = 1 ∨ c.utf8Size = 2 ∨ c.utf8Size = 3 ∨ c.utf8Size = 4 from by omega)
    with h | h | h | h
  · rw [String.utf8EncodeChar_eq_singleton h, List.mem_singleton] at hb
    subst hb
    have hle : c.val ≤ 0x7F := Char.utf8Size_eq_one_iff.mp h
    have hvn : c.val.toNat = c.toNat := Char.toNat_val c
    have hbb : c.val.toUInt8.toNat = c.toNat := by
      rw [UInt32.toNat_toUInt8, hvn]
      have : c.toNat ≤ 127 := by rw [← hvn]; exact UInt32.le_iff_toNat_le.mp hle
      omega
    have h34 : c.toNat ≠ 34 := fun he => hq (UInt32.toNat_inj.mp (by rw [hvn, he]; decide))
    have h92 : c.toNat ≠ 92 := fun he => hbs (UInt32.toNat_inj.mp (by rw [hvn, he]; decide))
    refine ⟨?_, ?_, ?_⟩
    · intro he; rw [← UInt8.toNat_inj, hbb, show (34 : UInt8).toNat = 34 from by decide] at he
      exact h34 he
    · intro he; rw [← UInt8.toNat_inj, hbb, show (92 : UInt8).toNat = 92 from by decide] at he
      exact h92 he
    · rw [UInt8.lt_iff_toNat_lt, hbb, show (32 : UInt8).toNat = 32 from by decide]; omega
  · rw [String.utf8EncodeChar_eq_cons_cons h] at hb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl <;> exact ⟨by bv_decide, by bv_decide, by bv_decide⟩
  · rw [String.utf8EncodeChar_eq_cons_cons_cons h] at hb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl <;> exact ⟨by bv_decide, by bv_decide, by bv_decide⟩
  · rw [String.utf8EncodeChar_eq_cons_cons_cons_cons h] at hb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl <;> exact ⟨by bv_decide, by bv_decide, by bv_decide⟩

/-- At the closing quote, `scanStr` finishes: it builds the body `arr[q0+1 .. q)` and unescapes
it exactly when an escape was seen. -/
theorem scanStr_close (arr : ByteArray) (q0 q : Nat) (esc : Bool) (hq : q < arr.size)
    (h34 : arr[q]! = 34) :
    scanStr arr q0 q esc =
      .ok (if esc then unescape (String.fromUTF8! (arr.extract (q0 + 1) q))
        else String.fromUTF8! (arr.extract (q0 + 1) q)) (q + 1) := by
  rw [getElem!_pos arr q hq] at h34
  rw [scanStr]
  simp only [dif_pos hq, h34, beq_self_eq_true, if_true]

/-- On a normal body byte (not quote, not backslash, not a control byte), `scanStr` advances one
byte with the escape flag unchanged. -/
theorem scanStr_normal_step (arr : ByteArray) (q0 q : Nat) (esc : Bool) (hq : q < arr.size)
    (h34 : arr[q]! ≠ 34) (h92 : arr[q]! ≠ 92) (hlt : ¬ arr[q]! < 32) :
    scanStr arr q0 q esc = scanStr arr q0 (q + 1) esc := by
  rw [getElem!_pos arr q hq] at h34 h92 hlt
  rw [scanStr]
  rw [dif_pos hq, if_neg (by simpa [beq_iff_eq] using h34),
    if_neg (by simpa [beq_iff_eq] using h92), if_neg hlt]

/-- `scanStr` walks a run of `k` consecutive scan-normal bytes, advancing `k` with the escape flag
unchanged. Iterates `scanStr_normal_step`. -/
theorem scanStr_normal_run (arr : ByteArray) (q0 q : Nat) (esc : Bool) : ∀ (k : Nat),
    (∀ i, i < k → q + i < arr.size ∧ arr[q + i]! ≠ 34 ∧ arr[q + i]! ≠ 92 ∧ ¬ arr[q + i]! < 32) →
    scanStr arr q0 q esc = scanStr arr q0 (q + k) esc := by
  intro k
  induction k generalizing q with
  | zero => intro _; rw [Nat.add_zero]
  | succ n ih =>
    intro hall
    obtain ⟨hq, h34, h92, hlt⟩ := hall 0 (by omega)
    rw [Nat.add_zero] at hq h34 h92 hlt
    rw [scanStr_normal_step arr q0 q esc hq h34 h92 hlt]
    rw [ih (q + 1) (fun i hi => by
      have := hall (i + 1) (by omega)
      rwa [show q + (i + 1) = q + 1 + i from by omega] at this)]
    rw [show q + 1 + n = q + (n + 1) from by omega]

/-- On a backslash starting a valid escape (`escEnd = some q'`), `scanStr` skips to `q'` and marks
the escape flag. -/
theorem scanStr_esc_step (arr : ByteArray) (q0 q q' : Nat) (esc : Bool) (hq : q < arr.size)
    (h92 : arr[q]! = 92) (hE : escEnd arr q = some q') :
    scanStr arr q0 q esc = scanStr arr q0 q' true := by
  rw [getElem!_pos arr q hq] at h92
  have c34 : (arr[q] == 34) = false := by simp [h92]
  have c92 : (arr[q] == 92) = true := by simp [h92]
  rw [scanStr]
  simp only [dif_pos hq, c34, c92, Bool.false_eq_true, if_false, if_true]
  split
  · rename_i q'' heq
    rw [hE] at heq; injection heq with h; rw [h]
  · rename_i heq
    rw [hE] at heq; exact absurd heq (by simp)

/-- A passthrough character (`escapeChar c = [c]`) is walked by `scanStr` over exactly its
`utf8Size` bytes, escape flag unchanged. -/
theorem scanStr_char_passthrough (arr : ByteArray) (q0 q : Nat) (esc : Bool) (c : Char)
    (hpass : escapeChar c = [c])
    (hcontent : ∀ j, j < c.utf8Size → arr[q + j]! = (String.utf8EncodeChar c)[j]!)
    (hbound : q + c.utf8Size ≤ arr.size) :
    scanStr arr q0 q esc = scanStr arr q0 (q + c.utf8Size) esc := by
  obtain ⟨h32, hq34, hq92⟩ := passthrough_props c hpass
  apply scanStr_normal_run arr q0 q esc c.utf8Size
  intro i hi
  have hlen : (String.utf8EncodeChar c).length = c.utf8Size := String.length_utf8EncodeChar c
  have hmem : (String.utf8EncodeChar c)[i]! ∈ String.utf8EncodeChar c := by
    rw [getElem!_pos _ i (by rw [hlen]; exact hi)]; exact List.getElem_mem _
  obtain ⟨hn34, hn92, hnlt⟩ := passthrough_bytes_normal c h32 hq34 hq92 _ hmem
  rw [hcontent i hi]
  exact ⟨by omega, hn34, hn92, hnlt⟩

end GripProps.ScanStr
