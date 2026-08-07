/-
Copyright (c) 2026 Jonathan Cubides. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Prieto-Cubides
-/
import GripProps.GradedMonad
import GripProps.Lawful
import GripProps.GradeSound
import GripProps.Productivity
import GripProps.ChoiceGrade
import GripProps.Scanner

/-!
# grip-props

Machine-checked metatheory for grip: the lawful graded-monad instances for `GParser`,
grade soundness, the totality-not-productivity gap, the impossible-grade result,
output-level correctness of the scanner, and completeness of the graded fixpoint.
Depends on grip + mathlib.
-/
