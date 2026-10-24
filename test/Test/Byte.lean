/-
Copyright (c) 2026 Jonathan Cubides. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Prieto-Cubides
-/
import Grip

/-! Checks for `Grip.Byte`, run at elaboration by `lake build Test`. -/

open Grip

-- A `conditional` parser weakened to `fallible` typechecks (see `Grip.Graded`).
example (f : UInt8 → Bool) : GParser fallible UInt8 := GParser.weakenFallible (GParser.satisfy f)
