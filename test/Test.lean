/-
Copyright (c) 2026 Jonathan Cubides. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Cubides
-/
import Grip

/-! Milestone 0 smoke test. `#guard` runs at elaboration, so a false guard is a build
error and turns the `core` CI job red. Real parser tests arrive in Milestone 1. -/

#guard (1 + 1 = 2)
