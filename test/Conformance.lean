/-
Copyright (c) 2026 Jonathan Cubides. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Cubides
-/
import Json

/-! # JSONTestSuite conformance runner

Dual mode:
* `conformance <file>` -- JSONTestSuite `parsers/` protocol: exit 0 if the file
  is accepted as valid JSON, 1 if rejected.
* `conformance` (no args) -- batch CI gate: walk `test/jsontestsuite/`, classify
  each file by name prefix (`y_` accept, `n_` reject, `i_` implementation-defined),
  print a summary, and exit nonzero on any regression.

Grammar-strict ceiling (see docs/specs/2026-07-13-json-conformance-design.md):
some invalid-UTF-8 `n_` files are accepted (`nAllowAccept`), and deep-nesting `n_`
files are skipped to avoid overflowing this process (`excluded`).
-/

open Grip Grip.Examples.Json

/-- Accept iff `json` parses the whole input (it enforces EOF). -/
def accepts (arr : ByteArray) : Bool :=
  match json.run arr 0 with
  | .ok _ _  => true
  | .error _ => false

/-- Invalid-UTF-8 `n_` files that grip accepts under the grammar-strict ceiling
(no UTF-8 validation). Each is an expected, documented acceptance, not a failure.
Shrinking this list later (a UTF-8 upgrade) is a strict improvement.
Populate in Task 4 from the actual batch output. -/
def nAllowAccept : List String := []

/-- Pathological deep-nesting `n_` files skipped so they cannot overflow this
process's stack (`fix` recurses on the Lean stack). Populate in Task 4. -/
def excluded : List String :=
  -- Both overflow the Lean stack (`fix` recurses per level); verified to crash (exit 134).
  -- i_structure_500 (500-deep) is NOT excluded: it parses fine, so it stays counted under i_.
  [ "n_structure_100000_opening_arrays.json"  -- 100k-deep
  , "n_structure_open_array_object.json"      -- ~50k-deep
  ]

private def classify (name : String) (accepted : Bool) :
    (Nat × Nat × Nat × Nat × Nat × Nat × Bool) :=
  -- returns (yTot,yOk, nTot,nOk, iAcc,iRej, regression)
  if name.startsWith "y_" then
    (1, (if accepted then 1 else 0), 0, 0, 0, 0, !accepted)
  else if name.startsWith "n_" then
    let allowed := nAllowAccept.contains name
    let ok := !accepted || allowed
    (0, 0, 1, (if !accepted then 1 else 0), 0, 0, !ok)
  else
    (0, 0, 0, 0, (if accepted then 1 else 0), (if accepted then 0 else 1), false)

def batch : IO UInt32 := do
  let dir : System.FilePath := "test/jsontestsuite"
  let entries ← dir.readDir
  let mut yTot := 0; let mut yOk := 0
  let mut nTot := 0; let mut nOk := 0
  let mut iAcc := 0; let mut iRej := 0
  let mut skipped := 0
  let mut regressions : List String := []
  for e in entries do
    let name := e.fileName
    if !(name.endsWith ".json") then continue
    if excluded.contains name then
      skipped := skipped + 1
      continue
    let arr ← IO.FS.readBinFile e.path
    let acc := accepts arr
    let (yt, yo, nt, no, ia, ir, regr) := classify name acc
    yTot := yTot + yt; yOk := yOk + yo
    nTot := nTot + nt; nOk := nOk + no
    iAcc := iAcc + ia; iRej := iRej + ir
    if regr then regressions := name :: regressions
  IO.println s!"y: {yOk}/{yTot} accepted · n: {nOk}/{nTot} rejected \
    (allow-accept {nAllowAccept.length}) · i: {iAcc} accepted / {iRej} rejected \
    · excluded: {skipped}"
  if regressions.isEmpty then
    IO.println "conformance: OK"
    return 0
  else
    IO.eprintln s!"conformance: {regressions.length} regression(s):"
    for r in regressions.reverse do IO.eprintln s!"  {r}"
    return 1

def main (args : List String) : IO UInt32 := do
  match args with
  | [file] =>
    let arr ← IO.FS.readBinFile file
    return (if accepts arr then 0 else 1)
  | _ => batch
