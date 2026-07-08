/-
Copyright 2026 Jonathan Cubides. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grip

/-!
# The impossible grade

The grade `impossible = ⟨never, always⟩` claims a parser that never errors and always
consumes. On empty input such a parser must succeed (never-error) yet must advance
(always-consume) -- but there is nothing to consume.

prim-parser makes this a clean impossibility: its size-indexed type forbids consuming
from `Text 0`, so `impossible` is uninhabited outright. grip's unindexed byte core does
not bound the result offset by the input size in the type, so it admits an out-of-bounds
liar (`fun _ q => .ok (a, q + 1)`), shown below. The impossibility therefore holds under
the bounds invariant that every real grip combinator satisfies but the type does not
enforce.
-/

open Grip

namespace Grip.ChoiceGrade

variable {α : Type}

/-- No bounds-respecting parser inhabits the `impossible` grade. On empty input `swit`
(never-error) forces a success and `cwit` (always-consume) forces the offset past 0,
but a bounds-respecting parser cannot advance past empty input. -/
theorem impossible_uninhabited (p : GParser impossible α)
    (bounded : ∀ {arr : ByteArray} {q : Nat} {a : α} {q' : Nat},
      p.run arr q = .ok (a, q') → q' ≤ arr.size) : False := by
  obtain ⟨a, q', h⟩ := p.swit rfl ByteArray.empty 0
  have hlt : 0 < q' := p.cwit h
  have hle : q' ≤ 0 := bounded h
  omega

/-- Without a bounds invariant, grip's unindexed type does admit an `impossible` parser:
this liar advances past end-of-input. It is why `impossible_uninhabited` needs the
`bounded` hypothesis; grip's real combinators (`satisfy`, `byte`, ...) all respect
input bounds. -/
def impossibleLiar (a : α) : GParser impossible α where
  run := fun _ q => .ok (a, q + 1)
  cwit := by
    intro arr q b q' h
    injection h with h1
    injection h1 with _ hq
    subst hq
    exact Nat.lt_succ_self q
  ewit := by intro he; exact absurd he (by decide)
  swit := by intro _ arr q; exact ⟨a, q + 1, rfl⟩

end Grip.ChoiceGrade
