/-
Copyright 2026 Jonathan Cubides. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Grip.Parser
import Grip.Char
import Grip.Ascii
import Grip.Combinators

/-!
# grip

A fast, graded Lean 4 byte-parser library. `import Grip` brings in the graded core and
`Parser` face (`Grip.Parser`), the UTF-8/`Char` layer (`Grip.Char`), the named byte
predicates and constants (`Grip.Ascii`), and the combinator vocabulary
(`Grip.Combinators`).
-/
