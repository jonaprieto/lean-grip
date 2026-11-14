/-
Copyright (c) 2026 Jonathan Cubides. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Prieto-Cubides
-/
import Lean.Compiler.NameDemangling

/-! Demangle compiled Lean symbols read one per line from stdin, for `tools/profile.py`.
Run through `lake env lean --run` rather than as a Lake target, so the package never links
the `Lean` library. Unknown symbols (C runtime, libc) are echoed unchanged. -/

/-- Print the demangled form of each stdin line, in order. -/
def main
    : IO Unit
    := do
  let stdin ← IO.getStdin
  repeat
    let line ← stdin.getLine
    if line.isEmpty then break
    let sym := line.trimAscii.toString
    IO.println ((Lean.Name.Demangle.demangleSymbol sym).getD sym)
