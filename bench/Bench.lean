/-
Copyright 2026 Jonathan Cubides. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# grip benchmark harness (Milestone 0 stub)

Times a trivial byte scan over `canada.json` so the harness, fixture, and CI wiring
exist before the first real combinator. Milestone 1 replaces the stub scan with the
real JSON parser. Run from the repo root: `lake exe bench`.
-/

/-- Stand-in "parse": count comma bytes (0x2c), starting the fold from `seed`. Replaced
by the real parser in M1. The `seed` parameter makes each call depend on a runtime value
so the scan cannot be hoisted out of the timing loop or memoized as loop-invariant; the
true comma count is the `seed = 0` result. -/
@[noinline] def stubParse (seed : Nat) (a : ByteArray) : Nat :=
  a.foldl (fun c b => if b == 44 then c + 1 else c) seed

/-- Best-of-`reps` wall time of `act` in milliseconds. `act` takes the iteration index so
the compiler cannot lift a loop-invariant computation out of the loop. Evaluating the
guard `act i == 0` forces the scan as an IO-sequenced effect between the two timestamps,
so the compiler cannot float the pure work past `t1`; the guard is never true here, but
that depends on the runtime input so it is not optimized away. Every iteration does the
full work. -/
def bestMs (reps : Nat) (act : Nat → Nat) : IO Float := do
  let mut best : Float := 0.0
  for i in [0:reps] do
    let t0 ← IO.monoNanosNow
    if act i == 0 then IO.eprintln "bench: unexpected empty scan"
    let t1 ← IO.monoNanosNow
    let dt := Float.ofNat (t1 - t0) / 1000000.0
    if i == 0 || dt < best then best := dt
  return best

def main : IO Unit := do
  let bytes ← IO.FS.readBinFile "bench/data/canada.json"
  let count := stubParse 0 bytes
  let ms ← bestMs 20 (fun i => stubParse i bytes)
  IO.println s!"count={count} parse_ms={ms}"
