/-
Copyright (c) 2026 Jonathan Cubides. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Cubides
-/
import Grip

/-!
# The impossible grade

The grade `impossible = ⟨never, always⟩` claims a parser that never errors and always
consumes. On empty input such a parser must succeed (never-error, by `swit`) yet must
advance (always-consume, by `cwit`) -- but there is nothing to consume.

`GParser` carries a fourth erased witness `bwit`: a success that starts in bounds ends in
bounds (`q ≤ arr.size → q' ≤ arr.size`). With it the impossibility holds *unconditionally*,
with no external hypothesis. Without `bwit`, grip's unindexed byte core would admit an
out-of-bounds liar (`fun _ q => .ok a (q + 1)`); `bwit` is exactly what rules it out, since
that liar cannot prove `q ≤ arr.size → q + 1 ≤ arr.size` (it fails at `q = arr.size`). This
recovers, from a single erased proof field, the guarantee that prim-parser's size-indexed
`Text n` type gives structurally.
-/

open Grip

namespace Grip.ChoiceGrade

variable {α : Type}

/-- No parser inhabits the `impossible` grade. On empty input, `swit` (never-error) forces a
success ending at some `q'`, `cwit` (always-consume) forces `0 < q'`, and `bwit` (bounds)
forces `q' ≤ ByteArray.empty.size = 0`; `0 < q' ≤ 0` is absurd. -/
theorem impossible_uninhabited (p : GParser impossible α) : False := by
  obtain ⟨a, q', h⟩ := p.swit rfl ByteArray.empty 0
  have hlt : 0 < q' := p.cwit h
  have hle : q' ≤ 0 := p.bwit (Nat.zero_le _) h
  omega

-- The out-of-bounds liar that `bwit` rules out. It no longer elaborates: its `bwit`
-- obligation is `q ≤ arr.size → q + 1 ≤ arr.size`, which fails at `q = arr.size`.
--   def impossibleLiar (a : α) : GParser impossible α where
--     run  := fun _ q => .ok a (q + 1)   -- cwit/ewit/swit provable as before, but
--     ...                                 -- bwit is UNPROVABLE: q + 1 ≤ arr.size does
--                                         -- not follow from q ≤ arr.size.

end Grip.ChoiceGrade
