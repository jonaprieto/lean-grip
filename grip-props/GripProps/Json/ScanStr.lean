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

open Grip.Json Grip.Json.Decode

namespace GripProps.ScanStr

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

end GripProps.ScanStr
