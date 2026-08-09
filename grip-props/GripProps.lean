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
import GripProps.ParserTypeEquiv
import GripProps.Json.Bytes
import GripProps.Json.NatDigits
import GripProps.Json.Number
import GripProps.Json.Parse
import GripProps.Json.Leaf
import GripProps.Json.ScanStr
import GripProps.Json.Container

/-!
# grip-props

Machine-checked metatheory for grip: the lawful graded-monad instances for `GParser`,
grade soundness, the totality-not-productivity gap, the impossible-grade result,
the parser-carrier equivalence audit, output-level correctness of the scanner,
and the JSON `parse ∘ render = id` theorem
(`GripProps.Container.parse_render`). Depends on grip + mathlib.
-/
