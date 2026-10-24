/-
Copyright (c) 2026 Jonathan Cubides. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Prieto-Cubides
-/
import Grip

/-! Checks for `Grip.Grade`, run at elaboration by `lake build Test`. -/

#guard (Grade.mul fallible fallible == fallible)
#guard (Grade.choice fallible fallible == fallible)
#guard (Grade.mul Grade.pure fallible == fallible)
#guard (Grade.mul fallible Grade.pure == fallible)
