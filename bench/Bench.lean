/-
Copyright (c) 2026 Jonathan Cubides. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Cubides
-/
import Json
import Sexp
import Lambda
import Http
import Toml
import Yaml
import Lean.Data.Json
import Std.Internal.Parsec.ByteArray

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
  | some d => d.tables.length
  | none   => 0

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

-- Cross-library reference: Lean's standard combinator library, `Std.Internal.Parsec`, on
-- the same validate-and-count task. A byte-level JSON leaf-counter matching grip's semantics
-- (number/string/keyword = 1 leaf, object keys not counted); counts 111130 on canada.json.
namespace StdParsecJson
open Std.Internal.Parsec Std.Internal.Parsec.ByteArray
abbrev P := Std.Internal.Parsec.ByteArray.Parser
@[inline] def isWs (b : UInt8) : Bool := b == 32 || b == 10 || b == 9 || b == 13
@[inline] def isNum (b : UInt8) : Bool :=
  (48 ≤ b && b ≤ 57) || b == 46 || b == 45 || b == 43 || b == 101 || b == 69
@[inline] def isAlpha (b : UInt8) : Bool := (97 ≤ b && b ≤ 122) || (65 ≤ b && b ≤ 90)
def ws : P Unit := do let _ ← many (satisfy isWs); pure ()
def number : P Nat := do let _ ← many (satisfy isNum); pure 1
def keyword : P Nat := do let _ ← many (satisfy isAlpha); pure 1
partial def strTail : P Unit := do let b ← any; if b == 34 then pure () else strTail
def pstring : P Nat := do let _ ← pbyte 34; strTail; pure 1
mutual
partial def value : P Nat := do
  ws
  match ← peek? with
  | some 123 => object
  | some 91  => array
  | some 34  => pstring
  | some 116 => keyword
  | some 102 => keyword
  | some 110 => keyword
  | some _   => number
  | none     => fail "eof"
partial def array : P Nat := do
  let _ ← pbyte 91; ws
  match ← peek? with
  | some 93 => do let _ ← any; pure 0
  | _ => do let n ← value; arrayTail n
partial def arrayTail (acc : Nat) : P Nat := do
  ws; let b ← any
  if b == 93 then pure acc
  else if b == 44 then do let n ← value; arrayTail (acc + n)
  else fail "array"
partial def object : P Nat := do
  let _ ← pbyte 123; ws
  match ← peek? with
  | some 125 => do let _ ← any; pure 0
  | _ => do let n ← pair; objectTail n
partial def pair : P Nat := do
  ws; let _ ← pbyte 34; strTail; ws; let _ ← pbyte 58; value
partial def objectTail (acc : Nat) : P Nat := do
  ws; let b ← any
  if b == 125 then pure acc
  else if b == 44 then do let n ← pair; objectTail (acc + n)
  else fail "object"
end
def json : P Nat := do let n ← value; ws; pure n
def parse (arr : ByteArray) : Except String Nat :=
  Std.Internal.Parsec.ByteArray.Parser.run json arr
end StdParsecJson

/-- `Std.Internal.Parsec` JSON leaf-counter driver (validate + count, like `parseJson`). -/
@[noinline] def parseStdParsec (arr : ByteArray) : Nat :=
  match StdParsecJson.parse arr with
  | .ok n => n
  | .error _ => 0

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
  -- JSON on canada.json: the main number, compared against lean4-parser.
  let jsonSrc ← IO.FS.readBinFile "bench/data/canada.json"
  let jsonCount := parseJson jsonSrc
  let jsonMs ← bestMs 20 (fun i => parseJson (barrier i jsonSrc))
  IO.println s!"count={jsonCount} parse_ms={jsonMs}"
  -- Cross-library reference on the same file/machine/toolchain: Lean's built-in
  -- Json.parse (builds a full DOM, so it does more than grip's validator).
  let jsonStr ← IO.FS.readFile "bench/data/canada.json"
  let ljMs ← bestMs 20 (fun i => parseLeanJson (barrierStr i jsonStr))
  IO.println s!"lean.json parse_ms={ljMs}"
  -- Cross-library reference: Lean's standard combinator library on the same task.
  let spCount := parseStdParsec jsonSrc
  let spMs ← bestMs 20 (fun i => parseStdParsec (barrier i jsonSrc))
  IO.println s!"std.parsec count={spCount} parse_ms={spMs}"
  -- TOML on a real file: a vendored Cargo.lock (count = number of [[package]] tables).
  let tomlSrc ← IO.FS.readBinFile "bench/data/cargo.lock"
  -- The remaining example parsers on generated inputs.
  benchOne "sexp"   ("(" ++ repeatStr "sym " 50000 ++ ")").toUTF8                     parseSexp
  benchOne "lambda" ("f" ++ repeatStr " x" 50000).toUTF8                              parseLambda
  benchOne "http"
    ("GET / HTTP/1.1\r\n" ++ repeatStr "X-H: v\r\n" 10000 ++ "\r\n").toUTF8 parseHttp
  benchOne "toml"   tomlSrc parseToml
  benchOne "yaml"   ("[" ++ repeatStr "x, " 30000 ++ "x]").toUTF8                     parseYaml
