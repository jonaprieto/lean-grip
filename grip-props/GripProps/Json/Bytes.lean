/-
Copyright (c) 2026 Jonathan Cubides. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Cubides
-/
import Mathlib

/-!
# ByteArray fold bridge

Lean 4.28's `ByteArray.foldl` is a bespoke monadic index loop with no library
characterization. This file bridges a full-range `ByteArray.foldl` to a `List.foldl` over the
underlying byte list (`arr.data.toList`), routing through the `Array` (`.data`) lemma set. It is
the foundation the `ByteArray`-level JSON round-trip lemmas rest on.
-/

set_option maxHeartbeats 1000000

namespace GripProps.Bytes

/-- The internal `foldlM` loop, in `Id`, computes the `List.foldl` over the remaining bytes. -/
theorem foldlM_loop_eq {β : Type} (f : β → UInt8 → β) (arr : ByteArray)
    (h : arr.size ≤ arr.size) :
    ∀ (i j : Nat) (b : β), j + i = arr.size →
      ByteArray.foldlM.loop (m := Id) (fun x y => pure (f x y)) arr arr.size h i j b
        = (arr.data.toList.drop j).foldl f b := by
  intro i
  induction i with
  | zero =>
    intro j b hj
    have hlen : arr.data.toList.length ≤ j := by
      rw [Array.length_toList, ByteArray.size_data]; omega
    unfold ByteArray.foldlM.loop
    have hnlt : ¬ j < arr.size := by omega
    rw [dif_neg hnlt, List.drop_eq_nil_of_le hlen]
    rfl
  | succ n ih =>
    intro j b hj
    have hjt : j < arr.data.toList.length := by
      rw [Array.length_toList, ByteArray.size_data]; omega
    unfold ByteArray.foldlM.loop
    have hlt : j < arr.size := by omega
    have hget : arr[j] = arr.data.toList[j]'hjt := by
      rw [ByteArray.getElem_eq_getElem_data, Array.getElem_toList]
    rw [dif_pos hlt]
    show ByteArray.foldlM.loop (m := Id) (fun x y => pure (f x y)) arr arr.size h n (j + 1)
        (f b arr[j]) = _
    rw [hget, List.drop_eq_getElem_cons hjt, List.foldl_cons]
    exact ih (j + 1) _ (by omega)

/-- A full-range `ByteArray.foldl` is the `List.foldl` over its byte list. -/
theorem foldl_eq_data_toList {β : Type} (f : β → UInt8 → β) (b : β) (arr : ByteArray) :
    arr.foldl f b 0 arr.size = arr.data.toList.foldl f b := by
  show (ByteArray.foldlM (m := Id) (fun x y => pure (f x y)) b arr 0 arr.size).run
      = arr.data.toList.foldl f b
  unfold ByteArray.foldlM
  simp only [Nat.le_refl, ↓reduceDIte, Nat.sub_zero]
  exact foldlM_loop_eq f arr (Nat.le_refl _) arr.size 0 b (by omega)

/-- The internal loop over a bounded range computes the `List.foldl` over that slice of bytes. -/
theorem foldlM_loop_range {β : Type} (f : β → UInt8 → β) (arr : ByteArray) (stop : Nat)
    (h : stop ≤ arr.size) :
    ∀ (i j : Nat) (b : β), j + i = stop →
      ByteArray.foldlM.loop (m := Id) (fun x y => pure (f x y)) arr stop h i j b
        = ((arr.data.toList.drop j).take i).foldl f b := by
  intro i
  induction i with
  | zero =>
    intro j b hj; unfold ByteArray.foldlM.loop
    simp only [List.take_zero, List.foldl_nil]; split <;> rfl
  | succ n ih =>
    intro j b hj
    have hjt : j < arr.data.toList.length := by
      rw [Array.length_toList, ByteArray.size_data]; omega
    have hget : arr[j] = arr.data.toList[j]'hjt := by
      rw [ByteArray.getElem_eq_getElem_data, Array.getElem_toList]
    unfold ByteArray.foldlM.loop
    rw [dif_pos (show j < stop by omega)]
    rw [hget, List.drop_eq_getElem_cons hjt, List.take_succ_cons, List.foldl_cons]
    exact ih (j + 1) _ (by omega)

/-- A bounded-range `ByteArray.foldl` is the `List.foldl` over that byte slice. -/
theorem foldl_range_data {β : Type} (f : β → UInt8 → β) (b : β) (arr : ByteArray) (q q' : Nat)
    (hq' : q' ≤ arr.size) (hqq : q ≤ q') :
    arr.foldl f b q q' = ((arr.data.toList.drop q).take (q' - q)).foldl f b := by
  show (ByteArray.foldlM (m := Id) (fun x y => pure (f x y)) b arr q q').run
      = ((arr.data.toList.drop q).take (q' - q)).foldl f b
  unfold ByteArray.foldlM
  simp only [dif_pos hq']
  exact foldlM_loop_range f arr q' hq' (q' - q) q b (by omega)

/-- The byte list of a `List Char`'s UTF-8 encoding is the per-character encodings concatenated. -/
theorem utf8Encode_data_toList (cs : List Char) :
    (List.utf8Encode cs).data.toList = cs.flatMap String.utf8EncodeChar := by
  induction cs with
  | nil => simp [List.utf8Encode_nil]
  | cons c cs ih =>
    rw [List.utf8Encode_cons, ByteArray.toList_data_append, ih, List.flatMap_cons]
    congr 1
    simp [List.utf8Encode]

/-- **String-bytes fold bridge.** Folding over a string's UTF-8 bytes is folding over the byte
list obtained by encoding each character. This turns any `ByteArray.foldl` over `s.toUTF8` (as in
`decodeNumberBytes?` and the parser) into a `List.foldl` over `s.toList`'s encoded bytes. -/
theorem toUTF8_foldl {β : Type} (f : β → UInt8 → β) (b : β) (s : String) :
    s.toUTF8.foldl f b 0 s.toUTF8.size
      = (s.toList.flatMap String.utf8EncodeChar).foldl f b := by
  rw [foldl_eq_data_toList,
    show s.toUTF8 = s.toList.utf8Encode from by
      rw [String.toUTF8_eq_toByteArray, ← String.utf8Encode_toList],
    utf8Encode_data_toList]

end GripProps.Bytes
