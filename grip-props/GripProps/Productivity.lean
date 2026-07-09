/-
Copyright (c) 2026 Jonathan Cubides. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Cubides
-/
import Grip

/-!
# Totality is not productivity

prim-parser's `fix` is kernel-total: its input is size-indexed (`Text n`), so the
recursion is well-founded on the length index and a non-productive body is caught as a
premature failure rather than a loop. See `PrimParser/Productivity.lean`.

grip's byte core trades size-indexing for `ByteArray` speed: `run` is
`ByteArray → Nat → ParseResult α`, with no length in the type. So `GParser.fix`
is `partial def`: a guarded body (one that consumes before reaching its recursive call,
as every real grammar does) terminates and is productive, but a left-recursive body
loops instead of failing. That is the honest limitation.

What the grade still guarantees, even for `partial` `fix`, is consumption soundness: the
runtime clamp downgrades a non-advancing success to a failure, so a success of `fix f`
always advances the offset. The `always`-consume grade never lies, which is what keeps
the `many`/`foldMany` gate sound over recursive parsers.
-/

open Grip

namespace Grip.Productivity

variable {α : Type}

/-- Consumption soundness of `fix`: every success of `GParser.fix f` advances the
offset, enforced by the runtime clamp despite `fix` being `partial`. This is the
guarantee that survives the loss of kernel totality. -/
theorem fix_advances (f : GParser conditional α → GParser conditional α)
    {arr : ByteArray} {q : Nat} {a : α} {q' : Nat}
    (h : (GParser.fix f).run arr q = .ok a q') : q < q' := (GParser.fix f).cwit h

end Grip.Productivity
