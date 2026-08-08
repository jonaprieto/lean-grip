/-
Copyright (c) 2026 Jonathan Cubides. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Prieto-Cubides
-/
import Json
import Grip.Json
import Sexp
import Lambda
import Http
import Toml
import Yaml
import Lean.Data.Json
import Std.Internal.Parsec.ByteArray

/-!
# grip benchmark harness

Times every example parser. The JSON matrix runs on the three vendored nativejson-benchmark
files; the other five run on inputs generated at startup. Each line is
`<lib> <dataset> count=<n> ms=<min> med=<median>` (or `<name> size=<bytes> ...` for the
generated inputs).

## Timing technique

`sampleMs` forces each parse as an IO-sequenced effect between two `monoNanosNow`
timestamps by evaluating `act i == 0`. The guard is never true at runtime but depends on
the result, so the compiler cannot hoist the work past `t1`. The barrier parameter `i`
prevents loop-invariant lifting. Twenty samples per cell; `ms` is the minimum, `med` the
median.
-/

open Grip

/-!
The benchmark contains intentionally direct recursive reference implementations. They are
measurement fixtures, not library APIs: retaining the same parser shape avoids benchmarking a
termination proof or a different traversal. The production `Grip` modules remain subject to the
partiality audit.
-/

/-- Repeat `s` `n` times by doubling, so building a large input is `O(n)` rather than the
`O(n^2)` of a left fold of `++`. -/
-- partiality: benchmark input generation uses a deliberately direct doubling loop; its fuel is
-- an implementation detail of the fixture and is not part of the parser API.
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

/-- Count leaf scalars of a `Lean.Json` tree (number/string/keyword = 1, object keys not
counted, containers sum their children), forcing the whole DOM. Mirrors `jsonLeaves`. -/
-- partiality: this is a cross-library benchmark mirror of the DOM traversal, not production code.
partial def leanJsonLeaves : Lean.Json → Nat
  | .null | .bool _ | .num _ | .str _ => 1
  | .arr xs  => xs.foldl (fun a j => a + leanJsonLeaves j) 0
  | .obj kvs => kvs.foldl (fun a _ v => a + leanJsonLeaves v) 0

/-- Cross-library reference: Lean's built-in `Lean.Json.parse`, plus the same leaf-count
traversal `parseGripJson` performs, so the DOM-vs-DOM rows do identical work. -/
@[noinline] def parseLeanJson (s : String) : Nat :=
  match Lean.Json.parse s with
  | .ok j    => leanJsonLeaves j
  | .error _ => 0

/-- Count leaf nodes of a `Grip.Json.Json` tree (number/string/keyword = 1, containers sum
their children), forcing the whole DOM. Matches the validators' leaf count for a sanity
cross-check. -/
-- partiality: this mirrors Grip's DOM traversal for the benchmark's like-for-like comparison.
partial def jsonLeaves : Grip.Json.Json → Nat
  | .null | .bool _ | .num _ _ | .str _ => 1
  | .arr xs  => xs.foldl (fun a j => a + jsonLeaves j) 0
  | .obj kvs => kvs.foldl (fun a kv => a + jsonLeaves kv.2) 0

/-- Fair DOM-vs-DOM peer to `parseLeanJson`: grip's value-producing `Grip.Json.parser`
builds the same kind of tree `Lean.Json.parse` does. Returns the forced leaf count. -/
@[noinline] def parseGripJson (arr : ByteArray) : Nat :=
  match Grip.Json.parser.run arr 0 with
  | .ok j _  => jsonLeaves j
  | .error _ => 0

/-- String barrier, mirroring `barrier` for the `String`-input `Lean.Json` driver. -/
@[noinline] def barrierStr (_k : Nat) (s : String) : String := s

/-- `@[noinline]` barrier: re-passes `b` each iteration so the timing loop cannot hoist
the work past the timestamp. -/
@[noinline] def barrier (_k : Nat) (b : ByteArray) : ByteArray := b

/-- Summary of `reps` timed runs: the minimum (noise floor) and the median (typical). -/
structure Stats where
  min    : Float
  median : Float

/-- Time `act` `reps` times and report min and median milliseconds. `act` receives the
iteration index so the compiler cannot memoize a loop-invariant result. Evaluating
`act i == 0` forces the parse between the two timestamps. -/
def sampleMs (reps : Nat) (act : Nat → Nat) : IO Stats := do
  let mut samples : Array Float := #[]
  for i in [0:reps] do
    let t0 ← IO.monoNanosNow
    if act i == 0 then IO.eprintln "bench: unexpected zero count"
    let t1 ← IO.monoNanosNow
    samples := samples.push (Float.ofNat (t1 - t0) / 1000000.0)
  let sorted := samples.qsort (· < ·)
  if sorted.isEmpty then return { min := 0.0, median := 0.0 }
  return { min := sorted[0]!, median := sorted[sorted.size / 2]! }

/-- Time one parser on `src` and print `<name> size=.. count=.. ms=.. med=..`. -/
def benchOne (name : String) (src : ByteArray) (p : ByteArray → Nat) : IO Unit := do
  let count := p src
  let s ← sampleMs 20 (fun i => p (barrier i src))
  IO.println s!"{name} size={src.size} count={count} ms={s.min} med={s.median}"

-- Cross-library reference: Lean's standard combinator library, `Std.Internal.Parsec`, on
-- the same validate-and-count task. A byte-level JSON leaf-counter matching grip's semantics
-- (number/string/keyword = 1 leaf, object keys not counted); counts 111130 on canada.json.
-- Strict RFC-8259 grammar: number/string/keyword validated identically to grip.
namespace StdParsecJson
open Std.Internal.Parsec Std.Internal.Parsec.ByteArray
abbrev P := Std.Internal.Parsec.ByteArray.Parser
@[inline] def isWs (b : UInt8) : Bool := b == 32 || b == 10 || b == 9 || b == 13
@[inline] def isDigit (b : UInt8) : Bool := 48 ≤ b && b ≤ 57
@[inline] def isDigit19 (b : UInt8) : Bool := 49 ≤ b && b ≤ 57
@[inline] def isHex (b : UInt8) : Bool :=
  isDigit b || (97 ≤ b && b ≤ 102) || (65 ≤ b && b ≤ 70)
-- Use the non-allocating `skipWhile`/`skipByte`, Std.Parsec's best byte-level idiom, rather
-- than `many (satisfy ..)`, which builds and discards an Array per token (a handicap that would
-- flatter grip). This is the fair comparison: each library at its best on the same task.
-- Since Lean v4.31, `skipWhile` reports `.eof` when the scan reaches the end of the input; up
-- to v4.30 it stopped there and succeeded. Recover at the position the scan already reached, so
-- a run that ends the document (the trailing whitespace before `eof`, digits in a bare `123`
-- document) behaves as it did before. Still O(1) per call, so the primitive stays the fast path.
@[inline] def skipRun (pred : UInt8 → Bool) : P Unit := fun it =>
  match skipWhile pred it with
  | .success it' u => .success it' u
  | .error it' _ => .success it' ()
def ws : P Unit := skipRun isWs
-- RFC number: `-? (0 | [1-9][0-9]*) frac? exp?`
def digits1 : P Unit := do
  let b ← any
  if isDigit b then skipRun isDigit else fail "digit"
def number : P Nat := do
  (do skipByte 45) <|> pure ()
  let b ← any
  if b == 48 then pure ()
  else if isDigit19 b then skipRun isDigit
  else fail "int"
  (do skipByte 46; digits1) <|> pure ()
  (attempt (do let e ← any
               if e == 101 || e == 69 then pure () else fail "exp"
               (do skipByte 43) <|> (do skipByte 45) <|> pure ()
               digits1) <|> pure ())
  pure 1
-- partiality: this benchmark parser preserves the direct recursive RFC string fixture.
-- RFC string: validate escapes including \uXXXX, reject control chars.
partial def strBody : P Unit := do
  let b ← any
  if b == 34 then pure ()
  else if b == 92 then do
    let c ← any
    if c == 34 || c == 92 || c == 47 || c == 98 || c == 102 ||
       c == 110 || c == 114 || c == 116 then strBody
    else if c == 117 then do
      let h1 ← any; let h2 ← any; let h3 ← any; let h4 ← any
      if isHex h1 && isHex h2 && isHex h3 && isHex h4 then strBody else fail "hex"
    else fail "escape"
  else if b < 32 then fail "control"
  else strBody
def skipStr : P Unit := do skipByte 34; strBody
def pstring : P Nat := do skipStr; pure 1
-- Exact keyword: match each byte of the full literal (first byte included).
def keywordLit (kw : List UInt8) : P Nat := do
  for c in kw do let b ← any; if b != c then fail "keyword"
  pure 1
mutual
-- partiality: these mutually recursive benchmark parsers preserve the measured parser shape.
partial def value : P Nat := do
  ws
  match ← peek? with
  | some 123 => object
  | some 91  => array
  | some 34  => pstring
  | some 116 => keywordLit [116, 114, 117, 101]
  | some 102 => keywordLit [102, 97, 108, 115, 101]
  | some 110 => keywordLit [110, 117, 108, 108]
  | some b   => if isDigit b || b == 45 then number else fail "value"
  | none     => fail "eof"
-- partiality: recursive array parsing is part of the benchmark fixture.
partial def array : P Nat := do
  let _ ← pbyte 91; ws
  match ← peek? with
  | some 93 => do let _ ← any; pure 0
  | _ => do let n ← value; arrayTail n
-- partiality: recursive array-tail parsing is part of the benchmark fixture.
partial def arrayTail (acc : Nat) : P Nat := do
  ws; let b ← any
  if b == 93 then pure acc
  else if b == 44 then do let n ← value; arrayTail (acc + n)
  else fail "array"
-- partiality: recursive object parsing is part of the benchmark fixture.
partial def object : P Nat := do
  let _ ← pbyte 123; ws
  match ← peek? with
  | some 125 => do let _ ← any; pure 0
  | _ => do let n ← pair; objectTail n
-- partiality: recursive pair parsing is part of the benchmark fixture.
partial def pair : P Nat := do
  ws; skipStr; ws; let _ ← pbyte 58; value
-- partiality: recursive object-tail parsing is part of the benchmark fixture.
partial def objectTail (acc : Nat) : P Nat := do
  ws; let b ← any
  if b == 125 then pure acc
  else if b == 44 then do let n ← pair; objectTail (acc + n)
  else fail "object"
end
def json : P Nat := do let n ← value; ws; eof; pure n
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
-- Strict RFC-8259 grammar: number/string/keyword validated identically to grip.
namespace HandScanner
@[inline] def isWs (b : UInt8) : Bool := b == 32 || b == 10 || b == 9 || b == 13
@[inline] def isDigit (b : UInt8) : Bool := 48 ≤ b && b ≤ 57
@[inline] def isDigit19 (b : UInt8) : Bool := 49 ≤ b && b ≤ 57
@[inline] def isHex (b : UInt8) : Bool :=
  isDigit b || (97 ≤ b && b ≤ 102) || (65 ≤ b && b ≤ 70)

-- partiality: the hand-written scanner is a direct benchmark baseline over an input position.
partial def skipWs (a : ByteArray) (i : Nat) : Nat :=
  if i < a.size then (if isWs a[i]! then skipWs a (i + 1) else i) else i
-- partiality: the hand-written scanner is a direct benchmark baseline over an input position.
partial def skipDigits (a : ByteArray) (i : Nat) : Nat :=
  if i < a.size && isDigit a[i]! then skipDigits a (i + 1) else i

/-- RFC number starting at `i`; `some end` or `none`. -/
-- partiality: the hand-written scanner is a direct benchmark baseline over an input position.
partial def scanNumber (a : ByteArray) (i0 : Nat) : Option Nat :=
  let i := if i0 < a.size && a[i0]! == 45 then i0 + 1 else i0
  if i < a.size && a[i]! == 48 then
    Id.run do
      let mut j := i + 1
      if j < a.size && a[j]! == 46 then
        let k := skipDigits a (j + 1)
        if k == j + 1 then return none
        j := k
      if j < a.size && (a[j]! == 101 || a[j]! == 69) then
        let mut k := j + 1
        if k < a.size && (a[k]! == 43 || a[k]! == 45) then k := k + 1
        let m := skipDigits a k
        if m == k then return none
        j := m
      return some j
  else if i < a.size && isDigit19 a[i]! then
    Id.run do
      let mut j := skipDigits a (i + 1)
      if j < a.size && a[j]! == 46 then
        let k := skipDigits a (j + 1)
        if k == j + 1 then return none
        j := k
      if j < a.size && (a[j]! == 101 || a[j]! == 69) then
        let mut k := j + 1
        if k < a.size && (a[k]! == 43 || a[k]! == 45) then k := k + 1
        let m := skipDigits a k
        if m == k then return none
        j := m
      return some j
  else none

/-- RFC string body starting just after the opening quote at `i`; `some end`
(index just past the closing quote) or `none`. Grammar-strict: validates
escapes and rejects control chars; does not validate UTF-8. -/
-- partiality: the hand-written scanner is a direct benchmark baseline over an input position.
partial def scanString (a : ByteArray) (i : Nat) : Option Nat :=
  if i < a.size then
    let b := a[i]!
    if b == 34 then some (i + 1)
    else if b == 92 then
      if i + 1 < a.size then
        let c := a[i + 1]!
        if c == 34 || c == 92 || c == 47 || c == 98 || c == 102 ||
           c == 110 || c == 114 || c == 116 then scanString a (i + 2)
        else if c == 117 then
          if i + 5 < a.size && isHex a[i + 2]! && isHex a[i + 3]! &&
             isHex a[i + 4]! && isHex a[i + 5]!
          then scanString a (i + 6) else none
        else none
      else none
    else if b < 32 then none
    else scanString a (i + 1)
  else none

/-- Exact keyword match at `i`; `some end` or `none`. -/
def scanKeyword (a : ByteArray) (i : Nat) (kw : List UInt8) : Option Nat :=
  let rec go (j : Nat) : List UInt8 → Option Nat
    | []      => some j
    | c :: cs => if j < a.size && a[j]! == c then go (j + 1) cs else none
  go i kw

mutual
-- partiality: these scanner functions form the benchmark's mutually recursive baseline.
/-- Parse one value after whitespace; return `(leafCount, nextPos)` or `none` on malformed. -/
partial def value (a : ByteArray) (i0 : Nat) : Option (Nat × Nat) :=
  let i := skipWs a i0
  if i < a.size then
    let b := a[i]!
    if b == 123 then object a (i + 1)
    else if b == 91 then array a (i + 1)
    else if b == 34 then (scanString a (i + 1)).map (fun j => (1, j))
    else if b == 116 then (scanKeyword a i [116, 114, 117, 101]).map (fun j => (1, j))
    else if b == 102 then (scanKeyword a i [102, 97, 108, 115, 101]).map (fun j => (1, j))
    else if b == 110 then (scanKeyword a i [110, 117, 108, 108]).map (fun j => (1, j))
    else if isDigit b || b == 45 then (scanNumber a i).map (fun j => (1, j))
    else none
  else none
-- partiality: recursive array scanning is part of the benchmark baseline.
partial def array (a : ByteArray) (i0 : Nat) : Option (Nat × Nat) :=
  let i := skipWs a i0
  if i < a.size && a[i]! == 93 then some (0, i + 1)
  else match value a i with
    | some (n, j) => arrayTail a j n
    | none => none
-- partiality: recursive array-tail scanning is part of the benchmark baseline.
partial def arrayTail (a : ByteArray) (i0 acc : Nat) : Option (Nat × Nat) :=
  let i := skipWs a i0
  if i < a.size then
    let b := a[i]!
    if b == 93 then some (acc, i + 1)
    else if b == 44 then match value a (i + 1) with
      | some (n, j) => arrayTail a j (acc + n)
      | none => none
    else none
  else none
-- partiality: recursive object scanning is part of the benchmark baseline.
partial def object (a : ByteArray) (i0 : Nat) : Option (Nat × Nat) :=
  let i := skipWs a i0
  if i < a.size && a[i]! == 125 then some (0, i + 1)
  else match pair a i with
    | some (n, j) => objectTail a j n
    | none => none
-- partiality: recursive pair scanning is part of the benchmark baseline.
partial def pair (a : ByteArray) (i0 : Nat) : Option (Nat × Nat) :=
  let i := skipWs a i0
  if i < a.size && a[i]! == 34 then
    match scanString a (i + 1) with
    | some k =>
      let i2 := skipWs a k
      if i2 < a.size && a[i2]! == 58 then value a (i2 + 1)
      else none
    | none => none
  else none
-- partiality: recursive object-tail scanning is part of the benchmark baseline.
partial def objectTail (a : ByteArray) (i0 acc : Nat) : Option (Nat × Nat) :=
  let i := skipWs a i0
  if i < a.size then
    let b := a[i]!
    if b == 125 then some (acc, i + 1)
    else if b == 44 then match pair a (i + 1) with
      | some (n, j) => objectTail a j (acc + n)
      | none => none
    else none
  else none
end

def parse (a : ByteArray) : Nat :=
  match value a 0 with
  | some (n, j) => if HandScanner.skipWs a j == a.size then n else 0
  | none => 0
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
  -- Per-dataset Lean matrix over the three nativejson-benchmark files: canada (number-heavy),
  -- citm_catalog (object/key-heavy), twitter (string/escape-heavy). grip, Std.Internal.Parsec,
  -- and the hand scanner do the identical strict validate-and-count (same leaf count per file);
  -- grip.json and lean.json both build a full DOM and count its leaves (identical heavier
  -- task). Each line is `<lib> <dataset> count=<n> ms=<min> med=<median>`; cross-language rows
  -- are in bench/cross-lang/.
  for (name, file) in [("canada", "bench/data/canada.json"),
                       ("citm", "bench/data/citm_catalog.json"),
                       ("twitter", "bench/data/twitter.json")] do
    let src ← IO.FS.readBinFile file
    let str ← IO.FS.readFile file
    let gc := parseJson src
    let gs ← sampleMs 20 (fun i => parseJson (barrier i src))
    IO.println s!"grip {name} count={gc} ms={gs.min} med={gs.median}"
    let sc := parseStdParsec src
    let ss ← sampleMs 20 (fun i => parseStdParsec (barrier i src))
    IO.println s!"std.parsec {name} count={sc} ms={ss.min} med={ss.median}"
    let hc := parseHand src
    let hs ← sampleMs 20 (fun i => parseHand (barrier i src))
    IO.println s!"hand {name} count={hc} ms={hs.min} med={hs.median}"
    let lc := parseLeanJson str
    let ls ← sampleMs 20 (fun i => parseLeanJson (barrierStr i str))
    IO.println s!"lean.json {name} count={lc} ms={ls.min} med={ls.median} (DOM build)"
    -- Fair DOM-vs-DOM: grip.json and lean.json both build a value tree and count its leaves.
    let gjc := parseGripJson src
    let gjs ← sampleMs 20 (fun i => parseGripJson (barrier i src))
    IO.println s!"grip.json {name} count={gjc} ms={gjs.min} med={gjs.median} (DOM build)"
  -- TOML on a real file: a vendored Cargo.lock (count = number of [[package]] tables).
  let tomlSrc ← IO.FS.readBinFile "bench/data/cargo.lock"
  -- The remaining example parsers on generated inputs.
  benchOne "sexp"   ("(" ++ repeatStr "sym " 50000 ++ ")").toUTF8                     parseSexp
  benchOne "lambda" ("f" ++ repeatStr " x" 50000).toUTF8                              parseLambda
  benchOne "http"
    ("GET / HTTP/1.1\r\n" ++ repeatStr "X-H: v\r\n" 10000 ++ "\r\n").toUTF8 parseHttp
  benchOne "toml"   tomlSrc parseToml
  benchOne "yaml"   ("[" ++ repeatStr "x, " 30000 ++ "x]").toUTF8                     parseYaml
