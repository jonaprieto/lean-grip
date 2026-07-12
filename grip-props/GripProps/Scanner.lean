/-
Copyright (c) 2026 Jonathan Cubides. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Cubides
-/
import Grip

/-!
# Functional correctness of the scanner

The grade metatheory (soundness, laws, bounds) says what a parser is *allowed* to do. This
file says what one actually *computes*: `scanFwd` (the loop under `takeWhile`) returns exactly
the maximal prefix of bytes satisfying the predicate. Two facts pin it down:

* `scanFwd_mem`  -- every byte it consumes satisfies the predicate;
* `scanFwd_stop` -- it stops at end-of-input or at the first byte that does not.

Together they characterize `scanFwd arr f q` as the least `k ≥ q` with `k = arr.size` or
`¬ f arr[k]`, i.e. the end of the maximal run. This is output-level correctness, independent
of the grade witnesses.
-/

open Grip

namespace Grip.Scanner

/-- Every byte `scanFwd` consumes satisfies the predicate `f`. -/
theorem scanFwd_mem (arr : ByteArray) (f : UInt8 → Bool) (q i : Nat)
    (hqi : q ≤ i) (hi : i < scanFwd arr f q) : f arr[i]! = true := by
  rw [scanFwd] at hi
  split at hi
  · rename_i h
    split at hi
    · rename_i hf
      by_cases hiq : i = q
      · rw [hiq, getElem!_pos arr q h]; exact hf
      · exact scanFwd_mem arr f (q + 1) i (by omega) hi
    · omega
  · omega
termination_by arr.size - q
decreasing_by omega

/-- `scanFwd` stops at end-of-input or at the first non-matching byte: starting in bounds, its
result is either `arr.size` or a position where `f` fails. -/
theorem scanFwd_stop (arr : ByteArray) (f : UInt8 → Bool) (q : Nat) (hq : q ≤ arr.size) :
    scanFwd arr f q = arr.size ∨ f arr[scanFwd arr f q]! = false := by
  rw [scanFwd]
  split
  · rename_i h
    split
    · exact scanFwd_stop arr f q.succ h
    · rename_i hf
      right
      rw [getElem!_pos arr q h]
      simpa using hf
  · left; omega
termination_by arr.size - q
decreasing_by omega

end Grip.Scanner
