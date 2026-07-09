/-
Copyright 2026 Jonathan Cubides. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Json
import Sexp
import Lambda
import Http
import Toml
import Yaml
import Lean.Data.Json

/-!
# grip benchmark harness

Times every example parser. JSON runs on `bench/data/canada.json` (~2.1 MB, the standard
nativejson-benchmark file, the number compared against lean4-parser); the other five run
on inputs generated at startup. Each line is `<name> size=<bytes> count=<n> ms=<best_of_20>`.

## Timing technique

`bestMs` forces each parse as an IO-sequenced effect between two `monoNanosNow`
timestamps by evaluating `act i == 0`. The guard is never true at runtime but depends on
the result, so the compiler cannot hoist the work past `t1`. The barrier parameter `i`
prevents loop-invariant lifting.
-/

open Grip

/-- Repeat `s` `n` times by doubling, so building a large input is `O(n)` rather than the
`O(n^2)` of a left fold of `++`. -/
partial def repeatStr (s : String) (n : Nat) : String :=
  if n == 0 then ""
  else if n == 1 then s
  else
    let half := repeatStr s (n / 2)
    let doubled := half ++ half
    if n % 2 == 0 then doubled else doubled ++ s

-- Per-parser drivers. Each returns a nonzero count on success (so the `bestMs` guard is
-- meaningful) and 0 on failure, and forces the full parse.

@[noinline] def parseJson (arr : ByteArray) : Nat :=
  match Grip.Examples.Json.json.run arr 0 with
  | .ok n _  => n
  | .error _ => 0

@[noinline] def parseSexp (arr : ByteArray) : Nat :=
  match Grip.Examples.Sexp.parse arr with
  | some (.list xs) => xs.length
  | some _          => 1
  | none            => 0

@[noinline] def parseLambda (arr : ByteArray) : Nat :=
  match Grip.Examples.Lambda.parse arr with
  | some _ => 1
  | none   => 0

@[noinline] def parseHttp (arr : ByteArray) : Nat :=
  match Grip.Examples.Http.parse arr with
  | some r => r.headers.length
  | none   => 0

@[noinline] def parseToml (arr : ByteArray) : Nat :=
  match Grip.Examples.Toml.parse arr with
  | some xs => xs.length
  | none    => 0

@[noinline] def parseYaml (arr : ByteArray) : Nat :=
  match Grip.Examples.Yaml.parse arr with
  | some (.seq xs) => xs.length
  | some _         => 1
  | none           => 0

/-- Cross-library reference: Lean's built-in `Lean.Json.parse`. It builds a full DOM (a
`Lean.Json` tree), so it does strictly more work than grip's validate-and-count; shown
for context on the same toolchain and machine. -/
@[noinline] def parseLeanJson (s : String) : Nat :=
  match Lean.Json.parse s with
  | .ok _    => 1
  | .error _ => 0

/-- String barrier, mirroring `barrier` for the `String`-input `Lean.Json` driver. -/
@[noinline] def barrierStr (_k : Nat) (s : String) : String := s

/-- `@[noinline]` barrier: re-passes `b` each iteration so the timing loop cannot hoist
the work past the timestamp. -/
@[noinline] def barrier (_k : Nat) (b : ByteArray) : ByteArray := b

/-- Best-of-`reps` wall time of `act` in milliseconds. `act` receives the iteration index
so the compiler cannot memoize a loop-invariant result. Evaluating `act i == 0` forces
the parse between the two timestamps. -/
def bestMs (reps : Nat) (act : Nat → Nat) : IO Float := do
  let mut best : Float := 0.0
  for i in [0:reps] do
    let t0 ← IO.monoNanosNow
    if act i == 0 then IO.eprintln "bench: unexpected zero count"
    let t1 ← IO.monoNanosNow
    let dt := Float.ofNat (t1 - t0) / 1000000.0
    if i == 0 || dt < best then best := dt
  return best

/-- Time one parser on `src` and print `<name> size=.. count=.. ms=..`. -/
def benchOne (name : String) (src : ByteArray) (p : ByteArray → Nat) : IO Unit := do
  let count := p src
  let ms ← bestMs 20 (fun i => p (barrier i src))
  IO.println s!"{name} size={src.size} count={count} ms={ms}"

def main (args : List String) : IO Unit := do
  -- `bench once [file]`: parse the file exactly once and exit -- no internal
  -- best-of loop, no input generation. This is the single work unit hyperfine is
  -- meant to sample (its warmup + repeated runs characterise end-to-end wall time,
  -- process startup and file IO included), unlike the self-timed suite below which
  -- loops 20x in-process and would make hyperfine measure the whole batch.
  if args.head? == some "once" then
    let file := args.getD 1 "bench/data/canada.json"
    let src ← IO.FS.readBinFile file
    IO.println s!"count={parseJson src}"
    return
  -- JSON on canada.json: the headline number, compared against lean4-parser.
  let jsonSrc ← IO.FS.readBinFile "bench/data/canada.json"
  let jsonCount := parseJson jsonSrc
  let jsonMs ← bestMs 20 (fun i => parseJson (barrier i jsonSrc))
  IO.println s!"count={jsonCount} parse_ms={jsonMs}"
  -- Cross-library reference on the same file/machine/toolchain: Lean's built-in
  -- Json.parse (builds a full DOM, so it does more than grip's validator).
  let jsonStr ← IO.FS.readFile "bench/data/canada.json"
  let ljMs ← bestMs 20 (fun i => parseLeanJson (barrierStr i jsonStr))
  IO.println s!"lean.json parse_ms={ljMs}"
  -- The other example parsers on generated inputs.
  benchOne "sexp"   ("(" ++ repeatStr "sym " 50000 ++ ")").toUTF8                     parseSexp
  benchOne "lambda" ("f" ++ repeatStr " x" 50000).toUTF8                              parseLambda
  benchOne "http"   ("GET / HTTP/1.1\r\n" ++ repeatStr "X-H: v\r\n" 10000 ++ "\r\n").toUTF8 parseHttp
  benchOne "toml"   (repeatStr "key = 123\n" 20000).toUTF8                            parseToml
  benchOne "yaml"   ("[" ++ repeatStr "x, " 30000 ++ "x]").toUTF8                     parseYaml
