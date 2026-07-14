/-
Copyright (c) 2026 Jonathan Cubides. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Cubides

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
advances the offset; the productive nesting depth is thus bounded by the bytes remaining and
the chosen fuel never truncates a guarded grammar (the grade that gives the clamp its
soundness is exactly what bounds the recursion). A guarded body -- one that consumes before
reaching its recursive call, as every real grammar does -- terminates with the right result; a
left-recursive body exhausts the fuel and fails. So the *totality* prim-parser buys with a
size index, grip buys with a grade-bounded fuel, keeping the `ByteArray` speed.

Totality is still not productivity: a left-recursive grammar cannot be accepted, and grip now
reports that as a clean failure (fuel exhaustion) rather than the `partial` loop it once was.
The guarantee that survives, and is proved below, is consumption soundness: the clamp makes
every success of `fix f` advance the offset, so the `always`-consume grade never lies, which is
what keeps the `many`/`foldMany` gate sound over recursive parsers.
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
