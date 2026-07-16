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

end GripProps.Parse
