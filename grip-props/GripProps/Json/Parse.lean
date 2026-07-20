/-
Copyright (c) 2026 Jonathan Cubides. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Cubides
-/
import Mathlib
import Grip.Json

/-!
# Parser run-denotation over a serialized prefix (L2, in progress)

The `parse ∘ render = id` proof runs the parser on `render v`'s bytes followed by an arbitrary
suffix, so each combinator needs a `run`-characterization on inputs of the form `sv ++ rest`.
This file starts that layer with the primitive byte combinators; the looping combinators
(`string`, `scanStr`, `foldMany`) and the `fix` unrolling for `value` are still TODO.
-/

set_option maxHeartbeats 1000000

open Grip

namespace GripProps.Parse

/-- `byte c` succeeds on `sv ++ rest` at an in-prefix position holding `c`, consuming one byte. -/
theorem byte_run_append (c : UInt8) (sv rest : ByteArray) (q : Nat)
    (hq : q < sv.size) (hc : sv[q] = c) :
    (GParser.byte c).run (sv ++ rest) q = .ok () (q + 1) := by
  have hqab : q < (sv ++ rest).size := by rw [ByteArray.size_append]; omega
  simp only [GParser.byte, dif_pos hqab, ByteArray.getElem_append_left hq, hc, beq_self_eq_true,
    if_true]

/-- `satisfy f` succeeds on `sv ++ rest` at an in-prefix byte satisfying `f`, returning it. -/
theorem satisfy_run_append (f : UInt8 → Bool) (sv rest : ByteArray) (q : Nat)
    (hq : q < sv.size) (hf : f sv[q] = true) :
    (GParser.satisfy f).run (sv ++ rest) q = .ok sv[q] (q + 1) := by
  have hqab : q < (sv ++ rest).size := by rw [ByteArray.size_append]; omega
  simp only [GParser.satisfy, dif_pos hqab, ByteArray.getElem_append_left hq, hf, if_true]

/-- At the end of the whole input, `eof` succeeds consuming nothing. -/
theorem eof_run_end (arr : ByteArray) (q : Nat) (hq : arr.size ≤ q) :
    (GParser.eof).run arr q = .ok () q := by
  simp only [GParser.eof, GParser.notFollowedBy, GParser.satisfy]
  rw [dif_neg (by omega : ¬ q < arr.size)]

/-- `scanFwd` consumes exactly a maximal run of `n` matching bytes ending at a non-match or EOF. -/
theorem scanFwd_run (arr : ByteArray) (f : UInt8 → Bool) (q n : Nat)
    (hall : ∀ i, i < n → f arr[q + i]! = true)
    (hstop : q + n = arr.size ∨ (q + n < arr.size ∧ f arr[q + n]! = false)) :
    scanFwd arr f q = q + n := by
  induction n generalizing q with
  | zero =>
    simp only [Nat.add_zero] at hstop ⊢
    rw [scanFwd]
    rcases hstop with h | ⟨h, hf⟩
    · rw [dif_neg (by omega)]
    · rw [dif_pos h, if_neg (by rw [← getElem!_pos arr q h]; simp [hf])]
  | succ n ih =>
    have hqs : q < arr.size := by omega
    have hf0 : f arr[q] = true := by
      rw [← getElem!_pos arr q hqs]; simpa using hall 0 (by omega)
    rw [scanFwd, dif_pos hqs, if_pos hf0,
      ih (q + 1)
        (fun i hi => by
          have := hall (i + 1) (by omega)
          rwa [show q + (i + 1) = q + 1 + i from by omega] at this)
        (by rcases hstop with h | ⟨h, hf⟩
            · exact Or.inl (by omega)
            · refine Or.inr ⟨by omega, ?_⟩
              rwa [show q + 1 + n = q + (n + 1) from by omega])]
    omega

/-- `takeWhile f` consumes a maximal run of `n` matching bytes. -/
theorem takeWhile_run (f : UInt8 → Bool) (arr : ByteArray) (q n : Nat)
    (hall : ∀ i, i < n → f arr[q + i]! = true)
    (hstop : q + n = arr.size ∨ (q + n < arr.size ∧ f arr[q + n]! = false)) :
    (GParser.takeWhile f).run arr q = .ok n (q + n) := by
  simp only [GParser.takeWhile, scanFwd_run arr f q n hall hstop, Nat.add_sub_cancel_left]

variable {α β γ : Type} {g g' : Grade}

/-- `ch c` on a matching in-prefix byte. -/
theorem ch_run_append (c : Char) (sv rest : ByteArray) (q : Nat)
    (hq : q < sv.size) (hc : sv[q] = Ascii.code c) :
    (GParser.ch c).run (sv ++ rest) q = .ok () (q + 1) :=
  byte_run_append _ sv rest q hq hc

/-- `pure a` consumes nothing. -/
theorem pure_run (a : α) (arr : ByteArray) (q : Nat) :
    (GParser.pure a).run arr q = .ok a q := rfl

/-- `map` on a successful sub-parse. -/
theorem map_run_ok (h : α → β) (x : GParser g α) (arr : ByteArray) (q : Nat) (a : α) (q' : Nat)
    (hx : x.run arr q = .ok a q') : (GParser.map h x).run arr q = .ok (h a) q' := by
  simp only [GParser.map, hx]

/-- `seqR` on two successes keeps the right value. -/
theorem seqR_run (x : GParser g α) (y : GParser g' β) (arr : ByteArray) (q : Nat) (a : α) (q' : Nat)
    (b : β) (q'' : Nat) (hx : x.run arr q = .ok a q') (hy : y.run arr q' = .ok b q'') :
    (GParser.seqR x y).run arr q = .ok b q'' := by
  simp only [GParser.seqR, hx, hy]

/-- `seqL` on two successes keeps the left value. -/
theorem seqL_run (x : GParser g α) (y : GParser g' β) (arr : ByteArray) (q : Nat) (a : α) (q' : Nat)
    (b : β) (q'' : Nat) (hx : x.run arr q = .ok a q') (hy : y.run arr q' = .ok b q'') :
    (GParser.seqL x y).run arr q = .ok a q'' := by
  simp only [GParser.seqL, hx, hy]

/-- `map2` on two successes combines the values. -/
theorem map2_run (f : α → β → γ) (x : GParser g α) (y : GParser g' β) (arr : ByteArray) (q : Nat)
    (a : α) (q' : Nat) (b : β) (q'' : Nat)
    (hx : x.run arr q = .ok a q') (hy : y.run arr q' = .ok b q'') :
    (GParser.map2 f x y).run arr q = .ok (f a b) q'' := by
  simp only [GParser.map2, hx, hy]

/-- `captureWith? f p`: `p` succeeds and `f` accepts the consumed range. -/
theorem captureWith?_run {δ : Type} (f : ByteArray → Nat → Nat → Option δ) (p : GParser g α)
    (arr : ByteArray) (q : Nat) (a : α) (q' : Nat) (d : δ)
    (hp : p.run arr q = .ok a q') (hf : f arr q q' = some d) :
    (GParser.captureWith? f p).run arr q = .ok d q' := by
  simp only [GParser.captureWith?, hp, hf]

/-- `bind` on a successful first parse continues with the second. -/
theorem bind_run (x : GParser g α) (f : α → GParser g' β) (arr : ByteArray) (q : Nat) (a : α)
    (q' : Nat) (r : ParseResult β) (hx : x.run arr q = .ok a q') (hf : (f a).run arr q' = r) :
    (GParser.bind x f).run arr q = r := by
  simp only [GParser.bind, hx, hf]

/-- `alt`, left branch succeeds. -/
theorem alt_run_left {ge gc ge' gc' : Modality} (x : GParser ⟨ge, gc⟩ α) (y : GParser ⟨ge', gc'⟩ α)
    (arr : ByteArray) (q : Nat) (a : α) (q' : Nat) (hx : x.run arr q = .ok a q') :
    (GParser.alt x y).run arr q = .ok a q' := by
  simp only [GParser.alt, hx]

/-- `alt`, left fails, right succeeds. -/
theorem alt_run_right {ge gc ge' gc' : Modality} (x : GParser ⟨ge, gc⟩ α)
    (y : GParser ⟨ge', gc'⟩ α) (arr : ByteArray) (q : Nat) (ex : Err) (a : α) (q' : Nat)
    (hx : x.run arr q = .error ex) (hy : y.run arr q = .ok a q') :
    (GParser.alt x y).run arr q = .ok a q' := by
  simp only [GParser.alt, hx, hy]

/-- `satisfy f` on an in-bounds byte satisfying `f` (stated with `getElem!`). -/
theorem satisfy_run! (f : UInt8 → Bool) (arr : ByteArray) (q : Nat) (hq : q < arr.size)
    (hf : f arr[q]! = true) : (GParser.satisfy f).run arr q = .ok arr[q]! (q + 1) := by
  rw [getElem!_pos arr q hq] at hf ⊢
  simp only [GParser.satisfy, dif_pos hq, hf, if_true]

/-- `byte c` on a matching in-bounds byte (stated with `getElem!`). -/
theorem byte_run! (c : UInt8) (arr : ByteArray) (q : Nat) (hq : q < arr.size)
    (hc : arr[q]! = c) : (GParser.byte c).run arr q = .ok () (q + 1) := by
  rw [getElem!_pos arr q hq] at hc
  simp only [GParser.byte, dif_pos hq, hc, beq_self_eq_true, if_true]

/-- `byte c` fails at an in-bounds non-matching byte. -/
theorem byte_run_fail! (c : UInt8) (arr : ByteArray) (q : Nat) (hq : q < arr.size)
    (hc : arr[q]! ≠ c) : (GParser.byte c).run arr q = .error ⟨q, []⟩ := by
  rw [getElem!_pos arr q hq] at hc
  simp only [GParser.byte, dif_pos hq]
  rw [if_neg (by simpa [beq_iff_eq] using hc)]

/-- `byte c` fails at end of input. -/
theorem byte_run_end (c : UInt8) (arr : ByteArray) (q : Nat) (hq : arr.size ≤ q) :
    (GParser.byte c).run arr q = .error ⟨q, []⟩ := by
  simp only [GParser.byte, dif_neg (Nat.not_lt.mpr hq)]

/-- `satisfy f` fails at an in-bounds non-satisfying byte. -/
theorem satisfy_run_fail! (f : UInt8 → Bool) (arr : ByteArray) (q : Nat) (hq : q < arr.size)
    (hf : f arr[q]! = false) : (GParser.satisfy f).run arr q = .error ⟨q, []⟩ := by
  rw [getElem!_pos arr q hq] at hf
  simp only [GParser.satisfy, dif_pos hq]; rw [if_neg (by simp [hf])]

/-- `satisfy f` fails at end of input. -/
theorem satisfy_run_end (f : UInt8 → Bool) (arr : ByteArray) (q : Nat) (hq : arr.size ≤ q) :
    (GParser.satisfy f).run arr q = .error ⟨q, []⟩ := by
  simp only [GParser.satisfy, dif_neg (Nat.not_lt.mpr hq)]

/-- `seqR`, left fails. -/
theorem seqR_run_fail_left (x : GParser g α) (y : GParser g' β) (arr : ByteArray) (q : Nat)
    (e : Err) (hx : x.run arr q = .error e) : (GParser.seqR x y).run arr q = .error e := by
  simp only [GParser.seqR, hx]

/-- `matchBytes` succeeds when `arr`'s bytes from `q` match `bs` from `i`. -/
theorem matchBytes_true (arr bs : ByteArray) (q i : Nat)
    (hsize : q + (bs.size - i) ≤ arr.size)
    (hmatch : ∀ j, i ≤ j → j < bs.size → arr[q + (j - i)]! = bs[j]!) :
    Grip.matchBytes arr bs i q = true := by
  rw [Grip.matchBytes]
  split
  · rename_i hi
    rw [if_pos (show q < arr.size by omega), Bool.and_eq_true]
    refine ⟨?_, ?_⟩
    · rw [beq_iff_eq]; simpa using hmatch i (le_refl i) hi
    · exact matchBytes_true arr bs (q + 1) (i + 1) (by omega) (fun j hj hjs => by
        have := hmatch j (by omega) hjs
        have he : q + 1 + (j - (i + 1)) = q + (j - i) := by omega
        rwa [he])
  · rfl
termination_by bs.size - i
decreasing_by omega

/-- `string s` (nonempty) succeeds when `arr`'s bytes from `q` match `s`'s UTF-8. -/
theorem string_run (s : String) (arr : ByteArray) (q : Nat)
    (hne : 0 < s.toUTF8.size) (hsize : q + s.toUTF8.size ≤ arr.size)
    (hmatch : ∀ j, j < s.toUTF8.size → arr[q + j]! = s.toUTF8[j]!) :
    (GParser.string s).run arr q = .ok () (q + s.toUTF8.size) := by
  have hmb : Grip.matchBytes arr s.toUTF8 0 q = true :=
    matchBytes_true arr s.toUTF8 q 0 (by simpa using hsize)
      (fun j _ hj => by simpa using hmatch j hj)
  simp only [GParser.string, hmb, if_true, if_pos (show q < q + s.toUTF8.size by omega)]

/-- `optional p`, `p` succeeds. -/
theorem optional_run_some (p : GParser g α) (arr : ByteArray) (q : Nat) (a : α) (q' : Nat)
    (hp : p.run arr q = .ok a q') : (GParser.optional p).run arr q = .ok (some a) q' := by
  simp only [GParser.optional]
  exact alt_run_left _ _ arr q (some a) q' (map_run_ok some p arr q a q' hp)

/-- `optional p`, `p` fails without consuming (grade forces same-offset failure); result `none`. -/
theorem optional_run_none (p : GParser g α) (arr : ByteArray) (q : Nat) (e : Err)
    (hp : p.run arr q = .error e) : (GParser.optional p).run arr q = .ok none q := by
  simp only [GParser.optional, GParser.alt, GParser.map, hp, GParser.pure]

/-- `ws` consumes nothing at a non-whitespace in-bounds byte. -/
theorem ws_run_stop (arr : ByteArray) (q : Nat) (hq : q < arr.size)
    (hw : Ascii.isWs arr[q] = false) :
    (GParser.ws).run arr q = .ok 0 q := by
  have : scanFwd arr Ascii.isWs q = q := by rw [scanFwd, dif_pos hq, if_neg (by simp [hw])]
  simp only [GParser.ws, GParser.takeWhile, this, Nat.sub_self]

/-- `ws` consumes nothing at end of input. -/
theorem ws_run_end (arr : ByteArray) (q : Nat) (hq : arr.size ≤ q) :
    (GParser.ws).run arr q = .ok 0 q := by
  have : scanFwd arr Ascii.isWs q = q := by rw [scanFwd, dif_neg (by omega)]
  simp only [GParser.ws, GParser.takeWhile, this, Nat.sub_self]

/-- `wsDispatch`, with no leading whitespace, runs the parser its `select` picks for the
current byte. -/
theorem wsDispatch_run_stop (select : UInt8 → GParser conditional Grip.Json.Json)
    (arr : ByteArray) (q : Nat) (hq : q < arr.size) (hw : Ascii.isWs arr[q] = false) :
    (Grip.Json.wsDispatch select).run arr q = (select arr[q]).run arr q := by
  have hs : scanFwd arr Ascii.isWs q = q := by rw [scanFwd, dif_pos hq, if_neg (by simp [hw])]
  simp only [Grip.Json.wsDispatch, hs, dif_pos hq]

/-- `wsByte b`, no leading whitespace, matching byte: consume it. -/
theorem wsByte_run_stop (b : UInt8) (arr : ByteArray) (q : Nat) (hq : q < arr.size)
    (hw : Ascii.isWs arr[q] = false) (hb : arr[q] = b) :
    (Grip.Json.wsByte b).run arr q = .ok () (q + 1) := by
  have hs : scanFwd arr Ascii.isWs q = q := by rw [scanFwd, dif_pos hq, if_neg (by simp [hw])]
  simp only [Grip.Json.wsByte, hs, dif_pos hq, hb, beq_self_eq_true, if_true]

/-- One-step unfolding of `fix`: its run is the body applied to the clamped self at the
bytes-remaining fuel, behind the advance clamp. -/
theorem fix_run_unroll (f : GParser conditional α → GParser conditional α) (arr : ByteArray)
    (q : Nat) :
    (GParser.fix f).run arr q
      = clampAdvance arr q ((f (GParser.fixSelf f (arr.size - q))).run arr q) := by
  show clampAdvance arr q (GParser.fixFuel f (arr.size - q + 1) arr q) = _
  rw [GParser.fixFuel_succ]

/-- The advance clamp is the identity on a success that advances within bounds. -/
theorem clampAdvance_ok (arr : ByteArray) (q : Nat) {v : Grip.Json.Json} {q' : Nat}
    (h1 : q < q') (h2 : q' ≤ arr.size) :
    clampAdvance arr q (.ok v q') = .ok v q' := by
  have h : q < q' ∧ q' ≤ arr.size := ⟨h1, h2⟩
  simp only [clampAdvance, if_pos h]

open Grip.Json Grip.Json.Decode Grip.Json.Json

/-- A `1-9` digit byte is a digit byte. -/
theorem isDigit19_isDigit {b : UInt8} (h : Ascii.isDigit19 b = true) : Ascii.isDigit b = true := by
  have h48 : ((48 : UInt8)).toNat = 48 := by decide
  have h49 : ((49 : UInt8)).toNat = 49 := by decide
  have h57 : ((57 : UInt8)).toNat = 57 := by decide
  simp only [Ascii.isDigit19, Ascii.isDigit, Bool.and_eq_true, decide_eq_true_eq,
    UInt8.le_iff_toNat_le, h48, h49, h57] at h ⊢
  omega

/-- A digit byte is not whitespace. -/
theorem isDigit_not_ws {b : UInt8} (h : Ascii.isDigit b = true) : Ascii.isWs b = false := by
  have hb : 48 ≤ b.toNat := by
    have h48 : ((48 : UInt8)).toNat = 48 := by decide
    simp only [Ascii.isDigit, Bool.and_eq_true, decide_eq_true_eq, UInt8.le_iff_toNat_le, h48] at h
    exact h.1
  have e : ∀ c : UInt8, c.toNat < 48 → (b == c) = false := fun c hc => by
    rw [beq_eq_false_iff_ne, ne_eq, ← UInt8.toNat_inj]; omega
  simp only [Ascii.isWs, e 32 (by decide), e 10 (by decide), e 9 (by decide), e 13 (by decide),
    Bool.or_self, Bool.or_false]

/-- `takeWhile1 f`: a nonempty maximal run of matching bytes. -/
theorem takeWhile1_run (f : UInt8 → Bool) (arr : ByteArray) (q n : Nat) (hq : q < arr.size)
    (hn : 1 ≤ n) (hall : ∀ i, i < n → f arr[q + i]! = true)
    (hstop : q + n = arr.size ∨ (q + n < arr.size ∧ f arr[q + n]! = false)) :
    (GParser.takeWhile1 f).run arr q = .ok n (q + n) := by
  have hf0 : f arr[q] = true := by
    rw [← getElem!_pos arr q hq]; simpa using hall 0 (by omega)
  show (if h : q < arr.size then
      if f arr[q] then (GParser.takeWhile f).run arr q else .error ⟨q, []⟩ else .error ⟨q, []⟩)
      = _
  rw [dif_pos hq, if_pos hf0]
  exact takeWhile_run f arr q n hall hstop

/-- `intPart` consumes a single leading `0`. -/
theorem intPart_run_zero (arr : ByteArray) (q : Nat) (hq : q < arr.size) (h0 : arr[q]! = 48) :
    intPart.run arr q = .ok () (q + 1) := by
  simp only [intPart]
  exact alt_run_left _ _ arr q () (q + 1) (byte_run! (Ascii.code '0') arr q hq (by rw [h0]; decide))

/-- `intPart` consumes a nonzero-leading integer (digit 1-9 then more digits). -/
theorem intPart_run_nonzero (arr : ByteArray) (q n : Nat) (hq : q < arr.size) (hn : 1 ≤ n)
    (h19 : Ascii.isDigit19 arr[q]! = true)
    (hall : ∀ i, 1 ≤ i → i < n → Ascii.isDigit arr[q + i]! = true)
    (hstop : q + n = arr.size ∨ (q + n < arr.size ∧ Ascii.isDigit arr[q + n]! = false)) :
    intPart.run arr q = .ok () (q + n) := by
  have hne : arr[q]! ≠ (48 : UInt8) := by
    intro he; rw [he] at h19; exact absurd h19 (by decide)
  simp only [intPart]
  refine alt_run_right _ _ arr q ⟨q, []⟩ () (q + n) (byte_run_fail! (Ascii.code '0') arr q hq ?_) ?_
  · simpa [show Ascii.code '0' = (48 : UInt8) from by decide] using hne
  · have hsat : (GParser.satisfy Ascii.isDigit19).run arr q = .ok arr[q]! (q + 1) :=
      satisfy_run! _ arr q hq h19
    have htw : (GParser.takeWhile Ascii.isDigit).run arr (q + 1) = .ok (n - 1) (q + n) := by
      have := takeWhile_run Ascii.isDigit arr (q + 1) (n - 1)
        (fun i hi => by have := hall (i + 1) (by omega) (by omega)
                        rwa [show q + (i + 1) = q + 1 + i from by omega] at this)
        (by rcases hstop with h | ⟨h, hf⟩
            · exact Or.inl (by omega)
            · exact Or.inr ⟨by omega, by rwa [show q + 1 + (n - 1) = q + n from by omega]⟩)
      rwa [show q + 1 + (n - 1) = q + n from by omega] at this
    exact seqR_run _ _ arr q _ (q + 1) () (q + n) hsat
      (seqR_run _ _ arr (q + 1) (n - 1) (q + n) () (q + n) htw rfl)

/-- `frac` consumes `.` then a nonempty digit run. -/
theorem frac_run (arr : ByteArray) (q n : Nat) (hq : q < arr.size) (hdot : arr[q]! = 46)
    (hq1 : q + 1 < arr.size) (hn : 2 ≤ n)
    (hall : ∀ i, 1 ≤ i → i < n → Ascii.isDigit arr[q + i]! = true)
    (hstop : q + n = arr.size ∨ (q + n < arr.size ∧ Ascii.isDigit arr[q + n]! = false)) :
    frac.run arr q = .ok (n - 1) (q + n) := by
  simp only [frac]
  have hch : (GParser.ch '.').run arr q = .ok () (q + 1) :=
    byte_run! (Ascii.code '.') arr q hq (by rw [hdot]; decide)
  have htw1 : (GParser.takeWhile1 Ascii.isDigit).run arr (q + 1) = .ok (n - 1) (q + n) := by
    have := takeWhile1_run Ascii.isDigit arr (q + 1) (n - 1) hq1 (by omega)
      (fun i hi => by have := hall (i + 1) (by omega) (by omega)
                      rwa [show q + (i + 1) = q + 1 + i from by omega] at this)
      (by rcases hstop with h | ⟨h, hf⟩
          · exact Or.inl (by omega)
          · exact Or.inr ⟨by omega, by rwa [show q + 1 + (n - 1) = q + n from by omega]⟩)
    rwa [show q + 1 + (n - 1) = q + n from by omega] at this
  exact seqR_run _ _ arr q () (q + 1) (n - 1) (q + n) hch htw1

/-- `value` parses a nonnegative integer number (`e = 0`). The `hstop` byte after the number is a
delimiter (not a digit, `.`, or `e`), so the optional fraction/exponent parsers correctly fail. -/
theorem value_run_num_int (arr : ByteArray) (q : Nat) (m : Int) (hm : 0 ≤ m) (n : Nat)
    (hn : 1 ≤ n) (hsize : q + n ≤ arr.size)
    (hstruct : (n = 1 ∧ arr[q]! = 48) ∨
      (Ascii.isDigit19 arr[q]! = true ∧ ∀ i, 1 ≤ i → i < n → Ascii.isDigit arr[q + i]! = true))
    (hstop : q + n = arr.size ∨ (q + n < arr.size ∧ Ascii.isDigit arr[q + n]! = false ∧
      arr[q + n]! ≠ 46 ∧ Ascii.isExp arr[q + n]! = false))
    (hdecode : decodeNumberBytes? arr q (q + n) = some (Json.num m 0)) :
    value.run arr q = .ok (Json.num m 0) (q + n) := by
  have hqs : q < arr.size := by omega
  have hd! : Ascii.isDigit arr[q]! = true := by
    rcases hstruct with ⟨_, h0⟩ | ⟨h19, _⟩
    · rw [h0]; decide
    · exact isDigit19_isDigit h19
  have hb : Ascii.isDigit arr[q] = true := by rwa [getElem!_pos arr q hqs] at hd!
  -- innerP consumes exactly [q, q+n)
  have hsign : (GParser.optional (GParser.ch '-')).run arr q = .ok none q :=
    optional_run_none _ arr q ⟨q, []⟩ (byte_run_fail! (Ascii.code '-') arr q hqs
      (by intro he; rw [show Ascii.code '-' = (45 : UInt8) from by decide] at he
          exact absurd (he ▸ hd! : Ascii.isDigit 45 = true) (by decide)))
  have hint : intPart.run arr q = .ok () (q + n) := by
    rcases hstruct with ⟨hn1, h0⟩ | ⟨h19, hds⟩
    · subst hn1; exact intPart_run_zero arr q hqs h0
    · refine intPart_run_nonzero arr q n hqs hn h19 hds ?_
      rcases hstop with h | ⟨h1, h2, _, _⟩
      · exact Or.inl h
      · exact Or.inr ⟨h1, h2⟩
  have hfrac : (GParser.optional frac).run arr (q + n) = .ok none (q + n) := by
    refine optional_run_none _ _ _ ⟨q + n, []⟩ (seqR_run_fail_left _ _ arr (q + n) _ ?_)
    rcases hstop with h | ⟨h1, _, hdot, _⟩
    · exact byte_run_end (Ascii.code '.') arr (q + n) (by omega)
    · exact byte_run_fail! (Ascii.code '.') arr (q + n) h1
        (by rwa [show Ascii.code '.' = (46 : UInt8) from by decide])
  have hexp : (GParser.optional expo).run arr (q + n) = .ok none (q + n) := by
    refine optional_run_none _ _ _ ⟨q + n, []⟩ (seqR_run_fail_left _ _ arr (q + n) _ ?_)
    rcases hstop with h | ⟨h1, _, _, hexp'⟩
    · exact satisfy_run_end _ arr (q + n) (by omega)
    · exact satisfy_run_fail! _ arr (q + n) h1 hexp'
  have hnum : number.run arr q = .ok (Json.num m 0) (q + n) := by
    simp only [number]
    exact captureWith?_run decodeNumberBytes? _ arr q () (q + n) (Json.num m 0)
      (seqR_run _ _ arr q none q () (q + n) hsign
        (seqL_run _ _ arr q () (q + n) none (q + n) hint
          (seqR_run _ _ arr (q + n) none (q + n) none (q + n) hfrac hexp))) hdecode
  have hne : ∀ c : UInt8, Ascii.isDigit c = false → ¬((arr[q] == c) = true) := fun c hc => by
    rw [beq_iff_eq]; intro he; rw [he, hc] at hb; exact absurd hb (by decide)
  rw [value, fix_run_unroll, wsDispatch_run_stop _ arr q hqs (isDigit_not_ws hb)]
  simp only [Ascii.lbrace, Ascii.lbracket, Ascii.quote, Ascii.dash]
  rw [if_neg (hne 123 (by decide)), if_neg (hne 91 (by decide)), if_neg (hne 34 (by decide)),
    if_neg (hne 116 (by decide)), if_neg (hne 102 (by decide)), if_neg (hne 110 (by decide)),
    if_pos (by rw [hb]; rfl)]
  rw [hnum]
  exact clampAdvance_ok arr q (by omega) (by omega)

/-- `value` parses a nonnegative fractional number (`e > 0`): integer part of length `ip`, `.`,
then a nonempty fractional part, total length `n`. -/
theorem value_run_num_frac (arr : ByteArray) (q : Nat) (m : Int) (e ip n : Nat) (hm : 0 ≤ m)
    (hip : 1 ≤ ip) (hn : ip + 2 ≤ n) (hsize : q + n ≤ arr.size)
    (hintstruct : (ip = 1 ∧ arr[q]! = 48) ∨
      (Ascii.isDigit19 arr[q]! = true ∧ ∀ i, 1 ≤ i → i < ip → Ascii.isDigit arr[q + i]! = true))
    (hdot : arr[q + ip]! = 46)
    (hfrac : ∀ i, ip + 1 ≤ i → i < n → Ascii.isDigit arr[q + i]! = true)
    (hstop : q + n = arr.size ∨ (q + n < arr.size ∧ Ascii.isDigit arr[q + n]! = false ∧
      arr[q + n]! ≠ 46 ∧ Ascii.isExp arr[q + n]! = false))
    (hdecode : decodeNumberBytes? arr q (q + n) = some (Json.num m e)) :
    value.run arr q = .ok (Json.num m e) (q + n) := by
  have hqs : q < arr.size := by omega
  have hd! : Ascii.isDigit arr[q]! = true := by
    rcases hintstruct with ⟨_, h0⟩ | ⟨h19, _⟩
    · rw [h0]; decide
    · exact isDigit19_isDigit h19
  have hb : Ascii.isDigit arr[q] = true := by rwa [getElem!_pos arr q hqs] at hd!
  have hsign : (GParser.optional (GParser.ch '-')).run arr q = .ok none q :=
    optional_run_none _ arr q ⟨q, []⟩ (byte_run_fail! (Ascii.code '-') arr q hqs
      (by intro he; rw [show Ascii.code '-' = (45 : UInt8) from by decide] at he
          exact absurd (he ▸ hd! : Ascii.isDigit 45 = true) (by decide)))
  -- intPart consumes [q, q+ip), stopping at the '.'
  have hint : intPart.run arr q = .ok () (q + ip) := by
    rcases hintstruct with ⟨hip1, h0⟩ | ⟨h19, hds⟩
    · subst hip1; exact intPart_run_zero arr q hqs h0
    · refine intPart_run_nonzero arr q ip hqs hip h19 hds (Or.inr ⟨by omega, ?_⟩)
      rw [hdot]; decide
  -- frac consumes [q+ip, q+n)
  have hfr : frac.run arr (q + ip) = .ok (n - ip - 1) (q + n) := by
    have := frac_run arr (q + ip) (n - ip) (by omega) hdot (by omega)
      (by omega)
      (fun i hi1 hi2 => by
        have := hfrac (ip + i) (by omega) (by omega)
        rwa [show q + (ip + i) = q + ip + i from by omega] at this)
      (by rcases hstop with h | ⟨h1, h2, _, _⟩
          · exact Or.inl (by omega)
          · exact Or.inr ⟨by omega, by rwa [show q + ip + (n - ip) = q + n from by omega]⟩)
    rwa [show q + ip + (n - ip) = q + n from by omega] at this
  have hexp : (GParser.optional expo).run arr (q + n) = .ok none (q + n) := by
    refine optional_run_none _ _ _ ⟨q + n, []⟩ (seqR_run_fail_left _ _ arr (q + n) _ ?_)
    rcases hstop with h | ⟨h1, _, _, hexp'⟩
    · exact satisfy_run_end _ arr (q + n) (by omega)
    · exact satisfy_run_fail! _ arr (q + n) h1 hexp'
  have hnum : number.run arr q = .ok (Json.num m e) (q + n) := by
    simp only [number]
    exact captureWith?_run decodeNumberBytes? _ arr q () (q + n) (Json.num m e)
      (seqR_run _ _ arr q none q () (q + n) hsign
        (seqL_run _ _ arr q () (q + ip) none (q + n) hint
          (seqR_run _ _ arr (q + ip) (some (n - ip - 1)) (q + n) none (q + n)
            (optional_run_some frac arr (q + ip) (n - ip - 1) (q + n) hfr) hexp))) hdecode
  have hne : ∀ c : UInt8, Ascii.isDigit c = false → ¬((arr[q] == c) = true) := fun c hc => by
    rw [beq_iff_eq]; intro he; rw [he, hc] at hb; exact absurd hb (by decide)
  rw [value, fix_run_unroll, wsDispatch_run_stop _ arr q hqs (isDigit_not_ws hb)]
  simp only [Ascii.lbrace, Ascii.lbracket, Ascii.quote, Ascii.dash]
  rw [if_neg (hne 123 (by decide)), if_neg (hne 91 (by decide)), if_neg (hne 34 (by decide)),
    if_neg (hne 116 (by decide)), if_neg (hne 102 (by decide)), if_neg (hne 110 (by decide)),
    if_pos (by rw [hb]; rfl)]
  rw [hnum]
  exact clampAdvance_ok arr q (by omega) (by omega)

/-- `value` parses the `null` keyword. -/
theorem value_run_null (arr : ByteArray) (q : Nat) (hq : q + 4 ≤ arr.size)
    (hm : ∀ j, j < 4 → arr[q + j]! = "null".toUTF8[j]!) :
    value.run arr q = .ok Json.null (q + 4) := by
  have hs : q < arr.size := by omega
  have hb : arr[q] = 110 := by
    have h0 := hm 0 (by norm_num)
    rw [Nat.add_zero, getElem!_pos arr q hs] at h0
    rw [h0]; decide
  have hstr : (GParser.string "null").run arr q = .ok () (q + 4) := by
    have := string_run "null" arr q (by decide) (by simpa using hq)
      (fun j hj => by have := hm j (by simpa using hj); simpa using this)
    simpa using this
  rw [value, fix_run_unroll, wsDispatch_run_stop _ arr q hs (by rw [hb]; decide), hb]
  simp only [Ascii.lbrace, Ascii.lbracket, Ascii.quote]
  rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide),
    if_neg (by decide), if_pos (by decide)]
  simp only [jnull, GParser.map, hstr]
  exact clampAdvance_ok arr q (by omega) (by omega)

/-- `value` parses the `true` keyword. -/
theorem value_run_true (arr : ByteArray) (q : Nat) (hq : q + 4 ≤ arr.size)
    (hm : ∀ j, j < 4 → arr[q + j]! = "true".toUTF8[j]!) :
    value.run arr q = .ok (Json.bool true) (q + 4) := by
  have hs : q < arr.size := by omega
  have hb : arr[q] = 116 := by
    have h0 := hm 0 (by norm_num); rw [Nat.add_zero, getElem!_pos arr q hs] at h0; rw [h0]; decide
  have hstr : (GParser.string "true").run arr q = .ok () (q + 4) := by
    have := string_run "true" arr q (by decide) (by simpa using hq)
      (fun j hj => by have := hm j (by simpa using hj); simpa using this)
    simpa using this
  rw [value, fix_run_unroll, wsDispatch_run_stop _ arr q hs (by rw [hb]; decide), hb]
  simp only [Ascii.lbrace, Ascii.lbracket, Ascii.quote]
  rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_pos (by decide)]
  simp only [jtrue, GParser.map, hstr]
  exact clampAdvance_ok arr q (by omega) (by omega)

/-- `value` parses the `false` keyword. -/
theorem value_run_false (arr : ByteArray) (q : Nat) (hq : q + 5 ≤ arr.size)
    (hm : ∀ j, j < 5 → arr[q + j]! = "false".toUTF8[j]!) :
    value.run arr q = .ok (Json.bool false) (q + 5) := by
  have hs : q < arr.size := by omega
  have hb : arr[q] = 102 := by
    have h0 := hm 0 (by norm_num); rw [Nat.add_zero, getElem!_pos arr q hs] at h0; rw [h0]; decide
  have hstr : (GParser.string "false").run arr q = .ok () (q + 5) := by
    have := string_run "false" arr q (by decide) (by simpa using hq)
      (fun j hj => by have := hm j (by simpa using hj); simpa using this)
    simpa using this
  rw [value, fix_run_unroll, wsDispatch_run_stop _ arr q hs (by rw [hb]; decide), hb]
  simp only [Ascii.lbrace, Ascii.lbracket, Ascii.quote]
  rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide),
    if_pos (by decide)]
  simp only [jfalse, GParser.map, hstr]
  exact clampAdvance_ok arr q (by omega) (by omega)

end GripProps.Parse
