/-
Copyright (c) 2026 Jonathan Cubides. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Prieto-Cubides
-/
import GripProps.Json.Container

/-!
## Trusted-axiom audit for the JSON round-trip theorem

CI compares this output with the expected Lean and quotient axioms. In particular, the theorem
must not depend on `sorryAx`, native evaluation, or compiler-trusted reduction.
-/

#print axioms GripProps.Container.parse_render
