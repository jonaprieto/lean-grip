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
-- Use the non-allocating `skipWhile`/`skipByte`, Std.Parsec's best byte-level idiom, rather
-- than `many (satisfy ..)`, which builds and discards an Array per token (a handicap that would
-- flatter grip). This is the fair comparison: each library at its best on the same task.
def ws : P Unit := skipWhile isWs
def number : P Nat := do skipWhile isNum; pure 1
def keyword : P Nat := do skipWhile isAlpha; pure 1
-- Escape-aware string body as a raw iterator scan (Std.Parsec's best: no per-byte monadic bind),
-- mirroring grip's `scanStrFwd`. `\X` is two bytes, so an escaped quote does not end the string.
partial def strEnd (it : ByteArray.Iterator) : ByteArray.Iterator :=
  if it.hasNext then
    let b := it.curr
    if b == 34 then it                                    -- unescaped closing quote
    else if b == 92 then (let it2 := it.next; if it2.hasNext then strEnd it2.next else it2)
    else strEnd it.next
  else it
def skipStrBody : P Unit := fun it => .success (strEnd it) ()
def skipStr : P Unit := do skipByte 34; skipStrBody; skipByte 34
def pstring : P Nat := do skipStr; pure 1
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
  ws; skipStr; ws; let _ ← pbyte 58; value
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

-- Hand-written byte-level JSON leaf-counter with NO combinators: recursion over `ByteArray`
-- with an explicit `Nat` position and a `Nat` count, `arr[i]!` for the byte read. Same
-- validate-and-count task and same 111130 count as the others; this is the "Lean runtime
-- floor" baseline (RC, bounds-checked indexing) that grip's combinator layer sits above.
namespace HandScanner
@[inline] def isWs (b : UInt8) : Bool := b == 32 || b == 10 || b == 9 || b == 13
@[inline] def isNumCh (b : UInt8) : Bool :=
  (48 ≤ b && b ≤ 57) || b == 46 || b == 45 || b == 43 || b == 101 || b == 69
@[inline] def isAlpha (b : UInt8) : Bool := (97 ≤ b && b ≤ 122) || (65 ≤ b && b ≤ 90)

partial def skipWs (a : ByteArray) (i : Nat) : Nat :=
  if i < a.size then (if isWs a[i]! then skipWs a (i + 1) else i) else i
partial def scanWhile (a : ByteArray) (p : UInt8 → Bool) (i : Nat) : Nat :=
  if i < a.size then (if p a[i]! then scanWhile a p (i + 1) else i) else i

mutual
/-- Parse one value after whitespace; return `(leafCount, nextPos)` or `none` on malformed. -/
partial def value (a : ByteArray) (i0 : Nat) : Option (Nat × Nat) :=
  let i := skipWs a i0
  if i < a.size then
    let b := a[i]!
    if b == 123 then object a (i + 1)          -- '{'
    else if b == 91 then array a (i + 1)        -- '['
    else if b == 34 then                        -- '"' string
      let j := scanWhile a (· != 34) (i + 1)
      if j < a.size then some (1, j + 1) else none
    else if b == 116 || b == 102 || b == 110 then some (1, scanWhile a isAlpha i)  -- t/f/n
    else if (48 ≤ b && b ≤ 57) || b == 45 then some (1, scanWhile a isNumCh i)     -- digit/'-'
    else none
  else none
partial def array (a : ByteArray) (i0 : Nat) : Option (Nat × Nat) :=
  let i := skipWs a i0
  if i < a.size && a[i]! == 93 then some (0, i + 1)         -- ']' empty
  else match value a i with
    | some (n, j) => arrayTail a j n
    | none => none
partial def arrayTail (a : ByteArray) (i0 acc : Nat) : Option (Nat × Nat) :=
  let i := skipWs a i0
  if i < a.size then
    let b := a[i]!
    if b == 93 then some (acc, i + 1)                       -- ']'
    else if b == 44 then match value a (i + 1) with          -- ','
      | some (n, j) => arrayTail a j (acc + n)
      | none => none
    else none
  else none
partial def object (a : ByteArray) (i0 : Nat) : Option (Nat × Nat) :=
  let i := skipWs a i0
  if i < a.size && a[i]! == 125 then some (0, i + 1)        -- '}' empty
  else match pair a i with
    | some (n, j) => objectTail a j n
    | none => none
partial def pair (a : ByteArray) (i0 : Nat) : Option (Nat × Nat) :=
  let i := skipWs a i0
  if i < a.size && a[i]! == 34 then                         -- key string (not counted)
    let k := scanWhile a (· != 34) (i + 1)
    if k < a.size then
      let i2 := skipWs a (k + 1)
      if i2 < a.size && a[i2]! == 58 then value a (i2 + 1)  -- ':' then value's count
      else none
    else none
  else none
partial def objectTail (a : ByteArray) (i0 acc : Nat) : Option (Nat × Nat) :=
  let i := skipWs a i0
  if i < a.size then
    let b := a[i]!
    if b == 125 then some (acc, i + 1)                      -- '}'
    else if b == 44 then match pair a (i + 1) with           -- ','
      | some (n, j) => objectTail a j (acc + n)
      | none => none
    else none
  else none
end

def parse (a : ByteArray) : Nat :=
  match value a 0 with | some (n, _) => n | none => 0
end HandScanner

/-- Hand-written scanner driver (validate + count, like `parseJson`). -/
@[noinline] def parseHand (arr : ByteArray) : Nat := HandScanner.parse arr

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
  -- Same task, no combinators: the hand-written Lean scanner (the runtime floor).
  let handCount := parseHand jsonSrc
  let handMs ← bestMs 20 (fun i => parseHand (barrier i jsonSrc))
  IO.println s!"hand count={handCount} parse_ms={handMs}"
  -- Challenging JSON datasets (nativejson-benchmark): citm_catalog (object/key/nesting-heavy)
  -- and twitter (string/Unicode/escape-heavy). grip vs Std.Internal.Parsec, both escape-aware.
  for (name, file) in [("citm", "bench/data/citm_catalog.json"),
                       ("twitter", "bench/data/twitter.json")] do
    let src ← IO.FS.readBinFile file
    let gc := parseJson src
    let gm ← bestMs 20 (fun i => parseJson (barrier i src))
    let sc := parseStdParsec src
    let sm ← bestMs 20 (fun i => parseStdParsec (barrier i src))
    IO.println s!"{name}: grip count={gc} ms={gm} | std.parsec count={sc} ms={sm}"
  -- TOML on a real file: a vendored Cargo.lock (count = number of [[package]] tables).
  let tomlSrc ← IO.FS.readBinFile "bench/data/cargo.lock"
  -- The remaining example parsers on generated inputs.
  benchOne "sexp"   ("(" ++ repeatStr "sym " 50000 ++ ")").toUTF8                     parseSexp
  benchOne "lambda" ("f" ++ repeatStr " x" 50000).toUTF8                              parseLambda
  benchOne "http"
    ("GET / HTTP/1.1\r\n" ++ repeatStr "X-H: v\r\n" 10000 ++ "\r\n").toUTF8 parseHttp
  benchOne "toml"   tomlSrc parseToml
  benchOne "yaml"   ("[" ++ repeatStr "x, " 30000 ++ "x]").toUTF8                     parseYaml
