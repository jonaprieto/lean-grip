/-
Copyright (c) 2026 Jonathan Cubides. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Prieto-Cubides

Inspired by prim-parser by Jan Mas Rovira
(https://github.com/janmasrovira/prim-parser, PrimParser/Basic.lean, commit
5a5ff0d, 2026-05-31): the discipline of encoding consumption and error
behaviour in a Grade index. The soundness theorems here are grip's own,
lifting grip's erased cwit/ewit/swit witness fields to named propositions.
-/
import Grip

/-!
# Grade soundness

The three erased witnesses on `GParser` are exactly the runtime facts its grade
predicts. These meta-theorems lift them to statements about arbitrary parsers, and pin
down that the grade is no longer a phantom index: a `conditional` parser that claims to
consume but does not is uninhabited.
-/

open Grip

namespace Grip.GradeSound

variable {α : Type}

/-- A `conditional` (always-consuming) parser advances the offset on every success. -/
theorem conditional_advances (p : GParser conditional α) {arr : ByteArray} {q : Nat}
    {a : α} {q' : Nat} (h : p.run arr q = .ok a q') : q < q' := p.cwit h

/-- A never-error parser always succeeds. -/
theorem neverError_succeeds {g : Grade} (hg : g.errors = never) (p : GParser g α)
    (arr : ByteArray) (q : Nat) : ∃ a q', p.run arr q = .ok a q' := p.swit hg arr q

/-- An always-error parser never succeeds. -/
theorem alwaysError_fails {g : Grade} (hg : g.errors = always) (p : GParser g α)
    (arr : ByteArray) (q : Nat) : ∃ e, p.run arr q = .error e := p.ewit hg arr q

/-- Grade soundness closes the consumption gap: a `conditional` parser cannot succeed
without advancing the offset. The "consumption liar" is uninhabited. -/
theorem no_consumption_liar (p : GParser conditional α) {arr : ByteArray} {q : Nat}
    {a : α} (h : p.run arr q = .ok a q) : False :=
  absurd (p.cwit h) (Nat.lt_irrefl q)

end Grip.GradeSound
