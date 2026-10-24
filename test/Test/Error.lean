/-
Copyright (c) 2026 Jonathan Cubides. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Prieto-Cubides
-/
import Grip

/-! Checks for `Grip.Error`, run at elaboration by `lake build Test`. -/

open Grip

#guard ParseError.message
    { pos := 0, line := 1, col := 1, expected := ["number", "number", "string"] }
    == "expected number or string"
