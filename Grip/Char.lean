/-
Copyright (c) 2026 Jonathan Cubides. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Prieto-Cubides
-/

import Grip.Graded

/-!
# Grip.Char: a UTF-8 / `Char` layer above the byte core

Consumers that think in `Char` rather than `UInt8` use these combinators. Each
decodes one UTF-8 scalar from the `ByteArray` and advances by its byte width, so the
fast path stays byte-level: there is no `String` allocation and no intermediate
decode of the whole input.

`satisfyChar`/`anyChar`/`char` are `conditional` (they consume at least one byte on
success). The `if q < q'` clamp in each `run` makes the always-consume witness hold
without reasoning about the decoder's width, mirroring `GParser.fix`. The decoder
`decodeUtf8` and the byte-level literal matcher `matchBytes` are exposed for grammars
that mix levels; `GParser.string` matches a whole UTF-8 literal.
-/

namespace Grip

open Grip

/-- Is `b` a UTF-8 continuation byte (`10xxxxxx`)? -/
@[inline] private def isCont (b : UInt8) : Bool := 0x80 ≤ b && b ≤ 0xBF

private def validSecond (b0 b1 : UInt8) : Bool :=
  if !isCont b1 then false
  else if b0 == 0xE0 then 0xA0 ≤ b1
  else if b0 == 0xED then b1 ≤ 0x9F
  else if b0 == 0xF0 then 0x90 ≤ b1
  else if b0 == 0xF4 then b1 ≤ 0x8F
  else true

/-- Decode one UTF-8 scalar starting at byte offset `q`, returning the `Char` and the
new offset `q + width` (width 1 to 4), or `none` on truncated or invalid input. -/
@[inline] def decodeUtf8 (arr : ByteArray) (q : Nat) : Option (Char × Nat) :=
  if h0 : q < arr.size then
    let b0 := arr[q]
    if b0 < 0x80 then
      some (Char.ofNat b0.toNat, q + 1)
    else if 0xC2 ≤ b0 && b0 ≤ 0xDF then
      if h1 : q + 1 < arr.size then
        let b1 := arr[q + 1]
        if validSecond b0 b1 then
          some (Char.ofNat (((b0.toNat &&& 0x1F) <<< 6) ||| (b1.toNat &&& 0x3F)), q + 2)
        else none
      else none
    else if 0xE0 ≤ b0 && b0 ≤ 0xEF then
      if h2 : q + 2 < arr.size then
        let b1 := arr[q + 1]
        let b2 := arr[q + 2]
        if validSecond b0 b1 && isCont b2 then
          some (Char.ofNat (((b0.toNat &&& 0x0F) <<< 12) |||
                            ((b1.toNat &&& 0x3F) <<< 6) ||| (b2.toNat &&& 0x3F)), q + 3)
        else none
      else none
    else if 0xF0 ≤ b0 && b0 ≤ 0xF4 then
      if h3 : q + 3 < arr.size then
        let b1 := arr[q + 1]
        let b2 := arr[q + 2]
        let b3 := arr[q + 3]
        if validSecond b0 b1 && isCont b2 && isCont b3 then
          some (Char.ofNat (((b0.toNat &&& 0x07) <<< 18) ||| ((b1.toNat &&& 0x3F) <<< 12) |||
                            ((b2.toNat &&& 0x3F) <<< 6) ||| (b3.toNat &&& 0x3F)), q + 4)
        else none
      else none
    else none
  else none

/-- A successful `decodeUtf8` ends within bounds: each branch that returns `some (c, q + k)`
first checks the byte at `q + (k-1)`, so `q + k ≤ arr.size`. -/
theorem decodeUtf8_le {arr : ByteArray} {q : Nat} {c : Char} {q' : Nat}
    (h : decodeUtf8 arr q = some (c, q')) : q' ≤ arr.size := by
  simp only [decodeUtf8] at h
  split at h
  · rename_i h0
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h; omega
    · split at h
      · split at h
        · rename_i h1
          split at h
          · simp only [Option.some.injEq, Prod.mk.injEq] at h; omega
          · exact absurd h (by simp)
        · exact absurd h (by simp)
      · split at h
        · split at h
          · rename_i h2
            split at h
            · simp only [Option.some.injEq, Prod.mk.injEq] at h; omega
            · exact absurd h (by simp)
          · exact absurd h (by simp)
        · split at h
          · rename_i h3
            split at h
            · split at h
              · simp only [Option.some.injEq, Prod.mk.injEq] at h; omega
              · exact absurd h (by simp)
            · exact absurd h (by simp)
          · exact absurd h (by simp)
  · exact absurd h (by simp)

/-- Consume one `Char` satisfying `p`, or fail without consuming. Grade `conditional`. -/
@[inline] def GParser.satisfyChar (p : Char → Bool) : GParser conditional Char where
  run arr q :=
    match decodeUtf8 arr q with
    | some (c, q') => if q < q' then (if p c then .ok c q' else .error ⟨q, []⟩) else .error ⟨q, []⟩
    | none => .error ⟨q, []⟩
  cwit := by
    intro arr q c q' h
    show q < q'
    split at h
    · rename_i r hd
      split at h
      · rename_i hlt
        split at h
        · rename_i hp
          simp only [ParseResult.ok.injEq] at h
          obtain ⟨_, rfl⟩ := h
          exact hlt
        · exact absurd h (by simp)
      · exact absurd h (by simp)
    · exact absurd h (by simp)
  ewit := by intro he; exact absurd he (by decide)
  swit := by intro he; exact absurd he (by decide)
  bwit := by
    intro arr q c q' hq h
    split at h
    · rename_i r hd
      split at h
      · rename_i hlt
        split at h
        · rename_i hp
          simp only [ParseResult.ok.injEq] at h
          obtain ⟨_, rfl⟩ := h
          exact decodeUtf8_le hd
        · exact absurd h (by simp)
      · exact absurd h (by simp)
    · exact absurd h (by simp)

/-- Consume any one `Char`. Grade `conditional`. -/
@[inline] def GParser.anyChar : GParser conditional Char := GParser.satisfyChar (fun _ => true)

/-- Consume the specific `Char` `c`. Grade `conditional`. -/
@[inline] def GParser.char (c : Char) : GParser conditional Char := GParser.satisfyChar (· == c)

/-- Do the bytes of `bs` from index `i` match `arr` from offset `q`? -/
def matchBytes (arr bs : ByteArray) (i q : Nat) : Bool :=
  if i < bs.size then
    if q < arr.size then (arr[q]! == bs[i]!) && matchBytes arr bs (i + 1) (q + 1) else false
  else true
termination_by bs.size - i
decreasing_by omega

/-- A successful `matchBytes` starting at a real index (`i < bs.size`) ends within bounds:
each matched byte requires `q < arr.size`, so `q + (bs.size - i) ≤ arr.size`. -/
theorem matchBytes_le (arr bs : ByteArray) (i q : Nat) (hi : i < bs.size)
    (h : matchBytes arr bs i q = true) : q + (bs.size - i) ≤ arr.size := by
  rw [matchBytes] at h
  rw [if_pos hi] at h
  split at h
  · rename_i hq
    rw [Bool.and_eq_true] at h
    obtain ⟨_, hrec⟩ := h
    by_cases hi1 : i + 1 < bs.size
    · have ih := matchBytes_le arr bs (i + 1) (q + 1) hi1 hrec
      omega
    · omega
  · exact absurd h (by simp)
termination_by bs.size - i
decreasing_by omega

/-- Match the UTF-8 bytes of the literal `s`, consuming them. Intended for a nonempty
literal (grade `conditional`); the `if q < q'` clamp fails an empty match. -/
@[inline] def GParser.string (s : String) : GParser conditional Unit where
  run arr q :=
    if matchBytes arr s.toUTF8 0 q then
      if q < q + s.toUTF8.size then .ok () (q + s.toUTF8.size) else .error ⟨q, []⟩
    else .error ⟨q, []⟩
  cwit := by
    intro arr q a q' h
    show q < q'
    split at h
    · split at h
      · rename_i hlt
        simp only [ParseResult.ok.injEq] at h
        obtain ⟨_, rfl⟩ := h
        exact hlt
      · exact absurd h (by simp)
    · exact absurd h (by simp)
  ewit := by intro he; exact absurd he (by decide)
  swit := by intro he; exact absurd he (by decide)
  bwit := by
    intro arr q a q' hq h
    split at h
    · rename_i hm
      split at h
      · rename_i hlt
        simp only [ParseResult.ok.injEq] at h
        obtain ⟨_, rfl⟩ := h
        have hi : 0 < s.toUTF8.size := by omega
        have hb := matchBytes_le arr s.toUTF8 0 q hi hm
        simpa using hb
      · exact absurd h (by simp)
    · exact absurd h (by simp)

end Grip

/-! ### Sanity guards. -/
section
open Grip

#guard (GParser.run? GParser.anyChar "aπ".toUTF8) == some 'a'
#guard (GParser.run? (GParser.char 'a') "abc".toUTF8) == some 'a'
#guard (GParser.run? (GParser.char 'x') "abc".toUTF8) == none
-- multibyte: 'π' is 2 UTF-8 bytes (0xCF 0x80); anyChar decodes it as one Char.
#guard (GParser.run? GParser.anyChar "π".toUTF8) == some 'π'
#guard decodeUtf8 (ByteArray.mk #[0xC2, 0x80]) 0 |>.isSome
#guard decodeUtf8 (ByteArray.mk #[0xE0, 0xA0, 0x80]) 0 |>.isSome
#guard decodeUtf8 (ByteArray.mk #[0xF0, 0x90, 0x80, 0x80]) 0 |>.isSome
#guard decodeUtf8 (ByteArray.mk #[0xC0, 0x80]) 0 == none
#guard decodeUtf8 (ByteArray.mk #[0xE0, 0x80, 0x80]) 0 == none
#guard decodeUtf8 (ByteArray.mk #[0xED, 0xA0, 0x80]) 0 == none
#guard decodeUtf8 (ByteArray.mk #[0xF4, 0x90, 0x80, 0x80]) 0 == none
#guard decodeUtf8 (ByteArray.mk #[0xF5, 0x80, 0x80, 0x80]) 0 == none
#guard (GParser.run? (GParser.string "true") "true!".toUTF8) == some ()
#guard (GParser.run? (GParser.string "true") "trur".toUTF8) == none

end
