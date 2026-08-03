/-
Copyright (c) 2026 Jonathan Cubides. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Prieto-Cubides

Inspired by prim-parser by Jan Mas Rovira
(https://github.com/janmasrovira/prim-parser, PrimParser/Basic.lean, commit
5a5ff0d, 2026-05-31): the goal of a total `fix` without `partial`. prim-parser
gets it by size-indexing on `Text n`; grip gets it by grade-bounded fuel. The
`fix_advances` theorem is grip's own consequence of that clamp.
-/
import Grip

/-!
# Totality is not productivity

prim-parser's `fix` is kernel-total by size-indexing its input (`Text n`): the recursion is
well-founded on the length index, so a non-productive body is caught as a premature failure
rather than a loop. See `PrimParser/Basic.lean`.

grip keeps the flat, fast core -- `run` is `ByteArray → Nat → ParseResult α`, with no length
in the type -- and still gets kernel totality, by a different route. `GParser.fix` recurses on
an explicit fuel (`GParser.fixFuel`), set to the bytes remaining (`arr.size - q + 1`). The
runtime clamp downgrades any non-advancing success to a failure, so every self-success
advances the offset. This makes the advertised `conditional` grade sound. Completeness is a
separate result: a `Guarded` proof must show that the particular body observes its
self-reference only at greater offsets. For such a body the input-bounded fuel truncates no
accepted parse. Direct left recursion instead exhausts the fuel and fails. Thus the *totality*
prim-parser buys with a size index, grip buys with explicit fuel while keeping the flat
`ByteArray` representation.

Totality is still not productivity. A directly left-recursive grammar reports fuel exhaustion
rather than looping. More generally, a non-guarded body can be sensitive to the fuel budget, as
`FixComplete.oscBody` demonstrates. The unconditional guarantee proved below is consumption
soundness: the clamp makes every success of `fix f` advance the offset, so the
`always`-consume grade never lies and the `many`/`foldMany` gate remains sound.
-/

open Grip

namespace Grip.Productivity

variable {α : Type}

/-- Consumption soundness of `fix`: every success of `GParser.fix f` advances the
offset, enforced by the runtime clamp. This is the guarantee that keeps `many`/`foldMany`
sound over recursive parsers. -/
theorem fix_advances (f : GParser conditional α → GParser conditional α)
    {arr : ByteArray} {q : Nat} {a : α} {q' : Nat}
    (h : (GParser.fix f).run arr q = .ok a q') : q < q' := (GParser.fix f).cwit h

end Grip.Productivity
