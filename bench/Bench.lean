/-
Copyright 2026 Jonathan Cubides. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Json

/-!
# grip benchmark harness (Milestone 1)

Reads `bench/data/canada.json`, parses it with the grip-combinator JSON parser
(`Grip.Examples.Json.json`), and prints `count=<nodes> parse_ms=<best_of_20>`.

The parser is built entirely from grip combinators: leaf parsers plus `fix` for
recursion and `foldMany` for array and object repetition.

## Timing technique

`bestMs` forces each parse as an IO-sequenced effect between two
`monoNanosNow` timestamps by evaluating `act i == 0`.  The guard is never
true at runtime but depends on the result, so the compiler cannot hoist the
work past `t1`.  The barrier parameter `i` prevents loop-invariant lifting.
-/

open Grip

/-- Parse `arr` from offset 0 using the grip combinator parser;
    return the leaf-value count, or 0 on failure. -/
@[noinline] private def parseJson (arr : ByteArray) : Nat :=
  match Grip.Examples.Json.json.run arr 0 with
  | .ok (n, _) => n
  | .error _   => 0

/-- `@[noinline]` barrier: re-passes `b` each iteration so the timing loop
    cannot hoist the work past the timestamp. -/
@[noinline] private def barrier (_k : Nat) (b : ByteArray) : ByteArray := b

/-- Best-of-`reps` wall time of `act` in milliseconds.  `act` receives the
    iteration index so the compiler cannot memoize a loop-invariant result.
    Evaluating `act i == 0` forces the parse between the two timestamps. -/
def bestMs (reps : Nat) (act : Nat → Nat) : IO Float := do
  let mut best : Float := 0.0
  for i in [0:reps] do
    let t0 ← IO.monoNanosNow
    if act i == 0 then IO.eprintln "bench: unexpected zero count"
    let t1 ← IO.monoNanosNow
    let dt := Float.ofNat (t1 - t0) / 1000000.0
    if i == 0 || dt < best then best := dt
  return best

def main : IO Unit := do
  let bytes ← IO.FS.readBinFile "bench/data/canada.json"
  let count := parseJson bytes
  let ms ← bestMs 20 (fun i => parseJson (barrier i bytes))
  IO.println s!"count={count} parse_ms={ms}"
