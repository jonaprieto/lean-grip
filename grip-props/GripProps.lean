/-
Copyright (c) 2026 Jonathan Cubides. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Cubides
-/
import GripProps.GradedMonad
import GripProps.Lawful
import GripProps.GradeSound
import GripProps.Productivity
import GripProps.ChoiceGrade
import GripProps.Scanner
import GripProps.Json.Leaf

/-!
# grip-props

Machine-checked metatheory for grip: the lawful graded-monad instances for `GParser`,
grade soundness, the totality-not-productivity gap, the impossible-grade result,
output-level correctness of the scanner, and the JSON leaf round-trips that back the
`parse ∘ render = id` proof (`GripProps.Json.Leaf`). Depends on grip + mathlib.
-/
