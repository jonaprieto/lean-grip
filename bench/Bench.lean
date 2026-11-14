/-
Copyright (c) 2026 Jonathan Cubides. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Prieto-Cubides
-/
import Sexp
import Lambda
import Http
import Toml
import Yaml

/-! # grip core benchmark harness

This benchmark exercises the core byte parser through the non-JSON example grammars, then each
core combinator on its own synthetic input (the `micro.*` rows), so the bench job diffs every
function PR vs base. The JSON workload, including the core Grip validator row and DOM
comparisons, lives in `lean-grip-json`.
-/

open Grip

def repeatStr
    (s : String)
    (n : Nat)
    : String
    :=
  String.join (List.replicate n s)

@[noinline]
def parseSexp
    (arr : ByteArray)
    : Nat
    :=
  match Grip.Examples.Sexp.parse arr with
  | some (.list xs) => xs.length
  | some _          => 1
  | none            => 0

@[noinline]
def parseLambda
    (arr : ByteArray)
    : Nat
    :=
  match Grip.Examples.Lambda.parse arr with
  | some _ => 1
  | none   => 0

@[noinline]
def parseHttp
    (arr : ByteArray)
    : Nat
    :=
  match Grip.Examples.Http.parse arr with
  | some r => r.headers.length
  | none   => 0

@[noinline]
def parseToml
    (arr : ByteArray)
    : Nat
    :=
  match Grip.Examples.Toml.parse arr with
  | some d => d.tables.length
  | none   => 0

@[noinline]
def parseYaml
    (arr : ByteArray)
    : Nat
    :=
  match Grip.Examples.Yaml.parse arr with
  | some (.seq xs) => xs.length
  | some _          => 1
  | none            => 0

/-! ## Combinator microbenchmarks

One parser per core function, each a top-level constant like a real grammar, run over input
that makes that function the inner loop. A row counts what it parsed so a wrong parse shows. -/

/-- The byte `a`, the element of most microbenchmark inputs. -/
@[inline] def byteA : UInt8 := 97

/-- The byte `b`, which the microbenchmark inputs use as a second element or a miss. -/
@[inline] def byteB : UInt8 := 98

/-- Run `p` from offset 0 and measure the result with `size`; zero on failure. -/
@[inline]
def runCount
    {g : Grade}
    {α : Type}
    (p : GParser g α)
    (size : α → Nat)
    (arr : ByteArray)
    : Nat
    :=
  (p.run? arr).elim 0 size

/-- `scanFwd` through `takeWhile`. -/
def microTakeWhile : GParser flexible Nat := GParser.takeWhile (· == byteA)

/-- `foldFwd` through `foldMany`, one byte per step. -/
def microFoldMany : GParser flexible Nat :=
  GParser.foldMany (fun n _ => n + 1) 0 (GParser.byte byteA)

/-- `many` building a list, one byte per element. -/
def microMany : GParser flexible (List Unit) := GParser.many (GParser.byte byteA)

/-- `alt` whose left branch fails on every element. -/
def microAlt : GParser flexible (List Unit) :=
  GParser.many (GParser.byte byteB <|> GParser.byte byteA)

/-- `seqR` (and so `bind`) over a two-byte element. -/
def microSeq : GParser flexible (List Unit) :=
  GParser.many (GParser.byte byteA *> GParser.byte byteB)

/-- `dispatch` on the leading byte. -/
def microDispatch : GParser flexible (List Unit) :=
  GParser.many (GParser.dispatch fun c =>
    if c == byteA then GParser.byte byteA else GParser.byte byteB)

/-- `capture` of a four-byte word per element. -/
def microCapture : GParser flexible (List String) :=
  GParser.many (GParser.capture (GParser.takeWhile1 (· == byteA)) <* GParser.byte Ascii.space)

/-- `string` matching a four-byte literal per element. -/
def microString : GParser flexible (List Unit) := GParser.many (GParser.string "abcd")

/-- `nat` decoding a five-digit number per element. -/
def microNat : GParser flexible (List Nat) :=
  GParser.many (GParser.nat <* GParser.byte Ascii.comma)

/-- `sepBy` over single-byte items. -/
def microSepBy : GParser flexible (List Unit) :=
  GParser.sepBy (GParser.byte byteA) (GParser.byte Ascii.comma)

/-- `fix`: a bracket tree, counting nodes. Wide input makes one recursive call per child; deep
input nests the calls. -/
def microFix : GParser conditional Nat :=
  GParser.fix fun tree =>
    (fun xs => xs.foldl (· + ·) 1) <$>
      (GParser.byte Ascii.lparen *> GParser.many tree <* GParser.byte Ascii.rparen)

/-- `satisfy` with a predicate, one byte per element. -/
def microSatisfy : GParser flexible (List UInt8) := GParser.many (GParser.satisfy Ascii.isLower)

/-- `map` over a one-byte parser, folded so no list is built. -/
def microMap : GParser flexible Nat :=
  GParser.foldMany (· + ·) 0 (GParser.map (fun _ => 1) (GParser.byte byteA))

/-- `bind`: the second byte is chosen from the first. -/
def microBind : GParser flexible (List Unit) :=
  GParser.many (GParser.bind (GParser.satisfy Ascii.isLower) fun c =>
    if c == byteA then GParser.byte byteB else GParser.byte byteA)

/-- `map2` over a two-byte element. -/
def microMap2 : GParser flexible (List Unit) :=
  GParser.many (GParser.map2 (fun _ _ => ()) (GParser.byte byteA) (GParser.byte byteB))

/-- `takeN` after a guard byte, four bytes per element. -/
def microTakeN : GParser flexible (List Unit) :=
  GParser.many (GParser.byte byteA *> GParser.takeN 3)

/-- `label` around a one-byte parser. -/
def microLabel : GParser flexible (List Unit) :=
  GParser.many (GParser.label "a" (GParser.byte byteA))

/-- `satisfyChar`, decoding one two-byte UTF-8 character per element. -/
def microSatisfyChar : GParser flexible (List Char) :=
  GParser.many (GParser.satisfyChar (·.toNat > 127))

/-- `captureWith`, handing each word's range to a length function. -/
def microCaptureWith : GParser flexible (List Nat) :=
  GParser.many
    (GParser.captureWith (fun _ q q' => q' - q) (GParser.takeWhile1 (· == byteA))
      <* GParser.byte Ascii.space)

/-- `captureWith?`, accepting every range. -/
def microCaptureWith? : GParser flexible (List Nat) :=
  GParser.many
    (GParser.captureWith? (fun _ q q' => some (q' - q)) (GParser.takeWhile1 (· == byteA))
      <* GParser.byte Ascii.space)

/-- `takeWhile1` per word. -/
def microTakeWhile1 : GParser flexible (List Nat) :=
  GParser.many (GParser.takeWhile1 (· == byteA) <* GParser.byte Ascii.space)

/-- `oneOf` over a two-byte set. -/
def microOneOf : GParser flexible (List UInt8) := GParser.many (GParser.oneOf [byteA, byteB])

/-- `noneOf` excluding a byte that never occurs. -/
def microNoneOf : GParser flexible (List UInt8) := GParser.many (GParser.noneOf [Ascii.comma])

/-- `between` brackets around one byte. -/
def microBetween : GParser flexible (List Unit) :=
  GParser.many (GParser.between (GParser.byte Ascii.lparen) (GParser.byte Ascii.rparen)
    (GParser.byte byteA))

/-- `endBy`: every item carries its separator. -/
def microEndBy : GParser flexible (List Unit) :=
  GParser.endBy (GParser.byte byteA) (GParser.byte Ascii.comma)

/-- `many1` over one byte. -/
def microMany1 : GParser conditional (List Unit) := GParser.many1 (GParser.byte byteA)

/-- `skipMany`, counting without a list. -/
def microSkipMany : GParser flexible Nat := GParser.skipMany (GParser.byte byteA)

/-- `skipMany1`, counting without a list. -/
def microSkipMany1 : GParser conditional Nat := GParser.skipMany1 (GParser.byte byteA)

/-- `optional` (and so `option` and `pure`): every other element has a trailing `b`. -/
def microOptional : GParser flexible (List (Option Unit)) :=
  GParser.many (GParser.byte byteA *> GParser.optional (GParser.byte byteB))

/-- `notFollowedBy` after each byte. -/
def microNotFollowedBy : GParser flexible (List Unit) :=
  GParser.many (GParser.byte byteA <* GParser.notFollowedBy (GParser.byte byteB))

/-- `manyTill` up to a closing byte. -/
def microManyTill : GParser conditional (List Unit) :=
  GParser.manyTill (GParser.byte byteA) (GParser.byte byteB)

/-- `chooseG`, where only the last alternative matches. -/
def microChooseG : GParser flexible (List Unit) :=
  GParser.many (GParser.chooseG (GParser.byte Ascii.comma)
    [GParser.byte byteB, GParser.byte byteA])

/-- `count` of `choice`, where only the last alternative matches. -/
def microChoice : Parser (List Unit) :=
  GParser.count 200000 (GParser.choice [GParser.byte Ascii.comma, GParser.byte byteB,
    GParser.byte byteA])

/-- `count` over the `Parser` (fallible) face. -/
def microCount : Parser (List Unit) := GParser.count 200000 (GParser.byte byteA)

/-- `tryCatch`, recovering from a failing first branch on every element. -/
def microTryCatch : Parser (List Unit) :=
  GParser.count 200000 (GParser.tryCatch (GParser.byte byteB) fun _ => GParser.byte byteA)

/-- `stringLit` per quoted element. -/
def microStringLit : GParser flexible (List Nat) :=
  GParser.many (GParser.stringLit <* GParser.byte Ascii.comma)

/-- `takeStringBody` over one long unterminated body. -/
def microTakeStringBody : GParser flexible Nat := GParser.takeStringBody

/-- Line count of the error `parse` reports at the end of many lines, plus its `pretty`
rendering: `mkParseError` scans the input for the line and column. -/
def microParseError
    (arr : ByteArray)
    : Nat
    :=
  match (GParser.skipMany (GParser.satisfy (· != 0)) *> GParser.byte 0).parse arr with
  | .error e => e.line + (e.pretty arr).length
  | .ok _ => 0

/-- `pure` after each byte, folded so no list is built. -/
def microPure : GParser flexible Nat :=
  GParser.foldMany (· + ·) 0 (GParser.byte byteA *> GParser.pure 1)

/-- `fail` as the left branch of every element. -/
def microFail : GParser flexible (List Unit) :=
  GParser.many (GParser.fail <|> GParser.byte byteA)

/-- `seqL` over a two-byte element. -/
def microSeqL : GParser flexible (List Unit) :=
  GParser.many (GParser.byte byteA <* GParser.byte byteB)

/-- `anyChar`, one two-byte character per element. -/
def microAnyChar : GParser flexible (List Char) := GParser.many GParser.anyChar

/-- `char`, matching one specific two-byte character per element. -/
def microChar : GParser flexible (List Char) := GParser.many (GParser.char 'λ')

/-- `ch`, matching an ASCII literal per element. -/
def microCh : GParser flexible (List Unit) := GParser.many (GParser.ch 'a')

/-- `ws` over one long whitespace run. -/
def microWs : GParser flexible Nat := GParser.ws

/-- `ws1` before each element. -/
def microWs1 : GParser flexible (List Unit) := GParser.many (GParser.ws1 *> GParser.byte byteA)

/-- `digit` per element. -/
def microDigit : GParser flexible (List UInt8) := GParser.many GParser.digit

/-- `hexDigit` per element. -/
def microHexDigit : GParser flexible (List UInt8) := GParser.many GParser.hexDigit

/-- `letter` per element. -/
def microLetter : GParser flexible (List UInt8) := GParser.many GParser.letter

/-- `alphaNum` per element. -/
def microAlphaNum : GParser flexible (List UInt8) := GParser.many GParser.alphaNum

/-- `upper` per element. -/
def microUpper : GParser flexible (List UInt8) := GParser.many GParser.upper

/-- `lower` per element. -/
def microLower : GParser flexible (List UInt8) := GParser.many GParser.lower

/-- One if the predicate holds. -/
@[inline] def bit (b : Bool) : Nat := if b then 1 else 0

/-- The `Ascii` predicates and value helpers, summed over every byte value. -/
def microAscii : GParser flexible Nat :=
  GParser.foldMany (· + ·) 0 (GParser.map (fun b =>
    bit (Ascii.isWs b) + bit (Ascii.isBlank b) + bit (Ascii.isDigit19 b)
      + bit (Ascii.isOctDigit b) + bit (Ascii.isExp b) + bit (Ascii.isSign b)
      + bit (Ascii.isControl b) + bit (Ascii.isPrint b) + bit (Ascii.isPunct b)
      + (if Ascii.isHexDigit b then Ascii.hexValue b else 0)
      + (if Ascii.isDigit b then Ascii.digitValue b else 0))
    (GParser.satisfy fun _ => true))

/-- `sepBy1` over single-byte items. -/
def microSepBy1 : GParser conditional (List Unit) :=
  GParser.sepBy1 (GParser.byte byteA) (GParser.byte Ascii.comma)

/-- `endBy1`: every item carries its separator. -/
def microEndBy1 : GParser conditional (List Unit) :=
  GParser.endBy1 (GParser.byte byteA) (GParser.byte Ascii.comma)

/-- `option`: every other element has a trailing `b`. -/
def microOption : GParser flexible (List Nat) :=
  GParser.many
    (GParser.byte byteA *> GParser.option 0 (GParser.map (fun _ => 1) (GParser.byte byteB)))

/-- `eof` tried after every byte; it fails until the last one. -/
def microEof : GParser flexible (List Unit) :=
  GParser.many (GParser.byte byteA <* (GParser.eof <|> GParser.pure ()))

/-- `throwErr`, recovered by `tryCatch` on every element. -/
def microThrowErr : Parser (List Unit) :=
  GParser.count 200000
    (GParser.tryCatch (GParser.throwErr { pos := 0 }) fun _ => GParser.byte byteA)

/-- The `Parser` monad: `do` notation over the fallible face. -/
def microParserDo : Parser (List UInt8) :=
  GParser.count 100000 do
    let x ← (GParser.byte byteA : Parser Unit)
    let y ← (GParser.satisfy Ascii.isLower : Parser UInt8)
    pure (if x == () then y else 0)

/-- `gdo`, the graded do-notation, over a two-byte element. -/
def microGdo : GParser flexible (List (UInt8 × UInt8)) :=
  GParser.many (gdo
    let a ← GParser.satisfy (· == byteA)
    let b ← GParser.satisfy (· == byteB)
    return (a, b))

/-- `gcast` around a one-byte parser. -/
def microGcast : GParser flexible (List Unit) :=
  GParser.many (GParser.gcast rfl (GParser.byte byteA))

/-- `weakenFallible` (and so `weaken`) per element, under `count`. -/
def microWeaken : Parser (List Unit) :=
  GParser.count 200000 (GParser.weakenFallible (GParser.byte byteA))

/-- `parse` on success: the `Except` wrapper and no error rendering. -/
def microParseOk
    (arr : ByteArray)
    : Nat
    :=
  match (GParser.skipMany (GParser.byte byteA)).parse arr with
  | .ok n => n
  | .error _ => 0

/-- `ParseError.message` on its own, over 10000 errors (the private line and column helpers
run under `micro.parseError`). -/
def microErrorMessage
    (arr : ByteArray)
    : Nat
    :=
  (List.range 10000).foldl (init := 0) fun acc i =>
    let e : ParseError := { pos := arr.size + i, line := i, col := 1, expected := ["x", "y"] }
    acc + e.message.length

structure Stats where
  min : Float
  median : Float

@[noinline] def barrier (_k : Nat) (src : ByteArray) : ByteArray := src

def sampleMs
    (reps : Nat)
    (act : Nat → Nat)
    : IO Stats
    := do
  let mut samples : Array Float := #[]
  for i in [0:reps] do
    let t0 ← IO.monoNanosNow
    if act i == 0 then IO.eprintln "bench: unexpected zero count"
    let t1 ← IO.monoNanosNow
    samples := samples.push (Float.ofNat (t1 - t0) / 1000000.0)
  let sorted := samples.qsort (· < ·)
  if sorted.isEmpty then return { min := 0.0, median := 0.0 }
  return { min := sorted[0]!, median := sorted[sorted.size / 2]! }

def benchOne
    (name : String)
    (src : ByteArray)
    (p : ByteArray → Nat)
    : IO Unit
    := do
  let count := p src
  let s ← sampleMs 20 (fun i => p (barrier i src))
  IO.println s!"{name} size={src.size} count={count} ms={s.min} med={s.median}"

def main
    : IO Unit
    := do
  benchOne "sexp" ("(" ++ repeatStr "sym " 50000 ++ ")").toUTF8 parseSexp
  benchOne "lambda" ("f" ++ repeatStr " x" 50000).toUTF8 parseLambda
  benchOne "http"
    ("GET / HTTP/1.1\r\n" ++ repeatStr "X-H: v\r\n" 10000 ++ "\r\n").toUTF8 parseHttp
  let tomlSrc ← IO.FS.readBinFile "bench/data/cargo.lock"
  benchOne "toml" tomlSrc parseToml
  benchOne "yaml" ("[" ++ repeatStr "x, " 30000 ++ "x]").toUTF8 parseYaml
  let as := (repeatStr "a" 200000).toUTF8
  benchOne "micro.takeWhile" as (runCount microTakeWhile id)
  benchOne "micro.foldMany" as (runCount microFoldMany id)
  benchOne "micro.many" as (runCount microMany List.length)
  benchOne "micro.alt" as (runCount microAlt List.length)
  benchOne "micro.seq" (repeatStr "ab" 100000).toUTF8 (runCount microSeq List.length)
  benchOne "micro.dispatch" as (runCount microDispatch List.length)
  benchOne "micro.capture" (repeatStr "aaaa " 40000).toUTF8 (runCount microCapture List.length)
  benchOne "micro.string" (repeatStr "abcd" 50000).toUTF8 (runCount microString List.length)
  benchOne "micro.nat" (repeatStr "12345," 33000).toUTF8 (runCount microNat List.length)
  benchOne "micro.sepBy" ("a" ++ repeatStr ",a" 100000).toUTF8 (runCount microSepBy List.length)
  benchOne "micro.fixWide" ("(" ++ repeatStr "()" 100000 ++ ")").toUTF8 (runCount microFix id)
  let nest := repeatStr "(" 1000 ++ repeatStr ")" 1000
  benchOne "micro.fixDeep" ("(" ++ repeatStr nest 100 ++ ")").toUTF8 (runCount microFix id)
  let ab := (repeatStr "ab" 100000).toUTF8
  let words := (repeatStr "aaaa " 40000).toUTF8
  benchOne "micro.satisfy" as (runCount microSatisfy List.length)
  benchOne "micro.map" as (runCount microMap id)
  benchOne "micro.bind" ab (runCount microBind List.length)
  benchOne "micro.map2" ab (runCount microMap2 List.length)
  benchOne "micro.takeN" as (runCount microTakeN List.length)
  benchOne "micro.label" as (runCount microLabel List.length)
  benchOne "micro.satisfyChar" (repeatStr "λ" 100000).toUTF8
    (runCount microSatisfyChar List.length)
  benchOne "micro.captureWith" words (runCount microCaptureWith List.length)
  benchOne "micro.captureWith?" words (runCount microCaptureWith? List.length)
  benchOne "micro.takeWhile1" words (runCount microTakeWhile1 List.length)
  benchOne "micro.oneOf" ab (runCount microOneOf List.length)
  benchOne "micro.noneOf" as (runCount microNoneOf List.length)
  benchOne "micro.between" (repeatStr "(a)" 66000).toUTF8 (runCount microBetween List.length)
  benchOne "micro.endBy" (repeatStr "a," 100000).toUTF8 (runCount microEndBy List.length)
  benchOne "micro.many1" as (runCount microMany1 List.length)
  benchOne "micro.skipMany" as (runCount microSkipMany id)
  benchOne "micro.skipMany1" as (runCount microSkipMany1 id)
  benchOne "micro.optional" (repeatStr "aab" 66000).toUTF8 (runCount microOptional List.length)
  benchOne "micro.notFollowedBy" as (runCount microNotFollowedBy List.length)
  benchOne "micro.manyTill" (repeatStr "a" 200000 ++ "b").toUTF8
    (runCount microManyTill List.length)
  benchOne "micro.chooseG" as (runCount microChooseG List.length)
  benchOne "micro.choice" as (runCount microChoice List.length)
  benchOne "micro.count" as (runCount microCount List.length)
  benchOne "micro.tryCatch" as (runCount microTryCatch List.length)
  benchOne "micro.stringLit" (repeatStr "\"abcd\"," 28000).toUTF8
    (runCount microStringLit List.length)
  benchOne "micro.takeStringBody" as (runCount microTakeStringBody id)
  benchOne "micro.parseError" (repeatStr "aaaa\n" 40000).toUTF8 microParseError
  let lambdas := (repeatStr "λ" 100000).toUTF8
  benchOne "micro.pure" as (runCount microPure id)
  benchOne "micro.fail" as (runCount microFail List.length)
  benchOne "micro.seqL" ab (runCount microSeqL List.length)
  benchOne "micro.anyChar" lambdas (runCount microAnyChar List.length)
  benchOne "micro.char" lambdas (runCount microChar List.length)
  benchOne "micro.ch" as (runCount microCh List.length)
  benchOne "micro.ws" (repeatStr " " 200000).toUTF8 (runCount microWs id)
  benchOne "micro.ws1" (repeatStr "  a" 66000).toUTF8 (runCount microWs1 List.length)
  let zs := (repeatStr "z" 200000).toUTF8
  benchOne "micro.digit" (repeatStr "5" 200000).toUTF8 (runCount microDigit List.length)
  benchOne "micro.hexDigit" (repeatStr "f" 200000).toUTF8 (runCount microHexDigit List.length)
  benchOne "micro.letter" zs (runCount microLetter List.length)
  benchOne "micro.alphaNum" zs (runCount microAlphaNum List.length)
  benchOne "micro.upper" (repeatStr "Z" 200000).toUTF8 (runCount microUpper List.length)
  benchOne "micro.lower" zs (runCount microLower List.length)
  benchOne "micro.ascii" (ByteArray.mk ((List.range 200000).map (·.toUInt8)).toArray)
    (runCount microAscii id)
  benchOne "micro.sepBy1" ("a" ++ repeatStr ",a" 100000).toUTF8 (runCount microSepBy1 List.length)
  benchOne "micro.endBy1" (repeatStr "a," 100000).toUTF8 (runCount microEndBy1 List.length)
  benchOne "micro.option" (repeatStr "aab" 66000).toUTF8 (runCount microOption List.length)
  benchOne "micro.eof" as (runCount microEof List.length)
  benchOne "micro.throwErr" as (runCount microThrowErr List.length)
  benchOne "micro.parserDo" ab (runCount microParserDo List.length)
  benchOne "micro.gdo" ab (runCount microGdo List.length)
  benchOne "micro.gcast" as (runCount microGcast List.length)
  benchOne "micro.weaken" as (runCount microWeaken List.length)
  benchOne "micro.parseOk" as microParseOk
  benchOne "micro.errorMessage" as microErrorMessage
