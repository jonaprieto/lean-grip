/-
Copyright (c) 2026 Jonathan Cubides. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Cubides

The inductive `Json` value type and the peek-then-branch (char-dispatched) recursive
descent are adapted from Examples/Json.lean in prim-parser by Jan Mas Rovira
(https://github.com/janmasrovira/prim-parser, commit d34c6f0, 2026-07-04): the
constructor shape and the dispatch-on-first-character structure.

The number representation follows Lean's `Lean.Data.Json.JsonNumber`: a number is an
exact `mantissa * 10 ^ (-exponent)` with `mantissa : Int` and `exponent : Nat`, so no
value is rounded (unlike a `Float`).

grip keeps the strict RFC-8259 grammar of `Grip.Examples.Json` and builds values with
`GParser.capture` over the flat byte core, rather than prim-parser's size-indexed vector.
-/

import Grip

/-!
# Grip.Json: a value-producing, RFC-8259 JSON parser

Where `Grip.Examples.Json` *validates* and returns a leaf count, this module builds a
real `Json` value (a DOM). `import Grip.Json`, then `Grip.Json.parse : ByteArray →
Except ParseError Json` (or `parse!` from a `String`).

## Design

The grammar is the same grammar-strict RFC-8259 one as `Grip.Examples.Json`: leading
zeros (`01`), trailing dots (`1.`), bare exponents (`1e`), trailing commas, bad
escapes and trailing garbage are all rejected. Each grammar arm additionally builds a
value:

- numbers are captured (`GParser.capture`) as their verbatim lexeme and decoded to an
  exact `.num mantissa exponent` (the value `mantissa * 10 ^ (-exponent)`); no `Float`
  is involved, so no value is rounded;
- strings are captured and their escapes decoded (`\n`, `\"`, `\uXXXX`, and UTF-16
  surrogate pairs);
- arrays and objects recurse through `GParser.fix`.

This parser materializes a tree, so it does not keep the flat, allocation-free fast
path of the validator. It is the convenience API; the validator remains the benchmark.
-/

namespace Grip.Json

open Grip

/-- A JSON value. A number is the exact rational `num mantissa exponent`, denoting
`mantissa * 10 ^ (-exponent)` with `mantissa : Int` and `exponent : Nat` (Lean's
`JsonNumber` shape); an integer literal `n` is `num n 0`. Nothing is rounded. -/
inductive Json where
  | null
  | bool (b : Bool)
  | num  (mantissa : Int) (exponent : Nat)
  | str  (s : String)
  | arr  (xs : List Json)
  | obj  (kvs : List (String × Json))
  deriving Repr, BEq, Inhabited

namespace Json

/-- Build an integer value: `int n = num n 0`. -/
@[inline] def int (n : Int) : Json := .num n 0

/-- The integer value, if this number has no fractional part. Strict: only `exponent = 0`
matches, so `20e-1` (parsed `num 20 1`, the value `2.0`) is not an integer, mirroring
`Lean.JsonNumber`. -/
def int? : Json → Option Int
  | .num m 0 => some m
  | _        => none

/-- Look up a key in an object (first match); `none` for a non-object or missing key. -/
def get? : Json → String → Option Json
  | .obj kvs, k => (kvs.find? (·.1 == k)).map (·.2)
  | _,       _  => none

/-- Index into an array; `none` for a non-array or an out-of-range index. -/
def at? : Json → Nat → Option Json
  | .arr xs, i => xs[i]?
  | _,       _ => none

end Json

namespace Decode

/-- State threaded through `unescape`'s single left fold. -/
private structure UState where
  out   : String := ""
  esc   : Bool := false   -- previous char was a lone backslash
  uLeft : Nat := 0        -- hex digits still expected in a `\uXXXX` (0 = not in one)
  uAcc  : Nat := 0        -- hex value accumulated so far
  hi    : Nat := 0        -- pending high surrogate (0 = none)

/-- One step of `unescape`. Handles simple escapes, `\uXXXX`, and a high/low surrogate
pair combined into one scalar. Assumes a grammar-validated body, so malformed input is
handled leniently rather than rejected. -/
private def uStep (st : UState) (c : Char) : UState :=
  if st.uLeft > 0 then
    let acc := st.uAcc * 16 + Grip.Ascii.hexValue (UInt8.ofNat c.toNat)
    if st.uLeft == 1 then
      if st.hi ≠ 0 then
        let full := 0x10000 + (st.hi - 0xD800) * 0x400 + (acc - 0xDC00)
        { st with out := st.out.push (Char.ofNat full), uLeft := 0, uAcc := 0, hi := 0 }
      else if 0xD800 ≤ acc && acc ≤ 0xDBFF then
        { st with uLeft := 0, uAcc := 0, hi := acc }
      else
        { st with out := st.out.push (Char.ofNat acc), uLeft := 0, uAcc := 0 }
    else
      { st with uLeft := st.uLeft - 1, uAcc := acc }
  else if st.esc then
    let st := { st with esc := false }
    if c == 'u' then { st with uLeft := 4, uAcc := 0 }
    else
      let d :=
        if c == 'n' then '\n'
        else if c == 't' then '\t'
        else if c == 'r' then '\r'
        else if c == 'b' then Char.ofNat 8
        else if c == 'f' then Char.ofNat 12
        else c   -- `"` `\` `/` decode to themselves
      { st with out := st.out.push d }
  else if c == '\\' then { st with esc := true }
  else { st with out := st.out.push c }

/-- Decode the escapes in a JSON string body (no surrounding quotes). -/
def unescape (s : String) : String := (s.foldl uStep {}).out

/-- Strip the surrounding quotes of a captured string literal, then decode its escapes. -/
def decodeString (raw : String) : String :=
  unescape (String.ofList ((raw.toList.drop 1).dropLast))

/-- State threaded through `decodeNumber`'s fold over the (sign-stripped) lexeme. -/
private structure NState where
  mant    : Nat := 0     -- integer and fractional digits as one natural
  fracLen : Nat := 0     -- number of fractional digits
  phase   : Nat := 0     -- 0 = integer part, 1 = fraction, 2 = exponent
  expNeg  : Bool := false
  expVal  : Nat := 0

/-- One step of the float decode. `+`/`-` only occur in the exponent (the leading sign
is stripped before the fold). -/
private def nStep (st : NState) (c : Char) : NState :=
  if c == '.' then { st with phase := 1 }
  else if c == 'e' || c == 'E' then { st with phase := 2 }
  else if c == '+' then st
  else if c == '-' then { st with expNeg := true }
  else
    let d := c.toNat - 48
    if st.phase == 0 then { st with mant := st.mant * 10 + d }
    else if st.phase == 1 then { st with mant := st.mant * 10 + d, fracLen := st.fracLen + 1 }
    else { st with expVal := st.expVal * 10 + d }

/-- Decode a validated JSON number lexeme to an exact `.num mantissa exponent`. A
nonnegative base-10 exponent is folded into the mantissa (so `2e3` is `num 2000 0`),
keeping `exponent : Nat`; a negative one becomes the exponent (`2.5` is `num 25 1`). -/
def decodeNumber (s : String) : Json :=
  let cs := s.toList
  let neg := cs.headD ' ' == '-'
  let body := if neg then cs.drop 1 else cs
  let st := body.foldl nStep {}
  let mant : Int := if neg then -(st.mant : Int) else st.mant
  let decExp : Int := (if st.expNeg then -(st.expVal : Int) else (st.expVal : Int)) - st.fracLen
  if decExp ≥ 0 then Json.num (mant * (10 ^ decExp.toNat)) 0
  else Json.num mant (-decExp).toNat

end Decode

open Decode

-- Leaf value parsers -----------------------------------------------------

@[inline] private def frac : GParser conditional Nat :=
  GParser.seqR (GParser.ch '.') (GParser.takeWhile1 Ascii.isDigit)

@[inline] private def expo : GParser conditional Nat :=
  GParser.seqR (GParser.satisfy Ascii.isExp)
    (GParser.seqR (GParser.optional (GParser.satisfy Ascii.isSign))
      (GParser.takeWhile1 Ascii.isDigit))

@[inline] private def intPart : GParser conditional Unit :=
  GParser.alt (GParser.ch '0')
    (GParser.seqR (GParser.satisfy Ascii.isDigit19)
      (GParser.seqR (GParser.takeWhile Ascii.isDigit) (GParser.pure ())))

/-- A JSON number, decoded to `.num`. The lexeme is captured verbatim and
decoded; leading-zero and trailing-garbage rejection come from the grammar and the
top-level EOF check. -/
private def number : GParser conditional Json :=
  GParser.map decodeNumber
    (GParser.capture
      (GParser.seqR (GParser.optional (GParser.ch '-'))
        (GParser.seqL intPart
          (GParser.seqR (GParser.optional frac) (GParser.optional expo)))))

/-- A validated JSON string literal, decoded to its `String` contents. -/
private def jstr : GParser conditional String :=
  GParser.map decodeString (GParser.capture GParser.stringLit)

private def jstring : GParser conditional Json := GParser.map Json.str jstr
private def jnull  : GParser conditional Json :=
  GParser.map (fun _ => Json.null) (GParser.string "null")
private def jtrue  : GParser conditional Json :=
  GParser.map (fun _ => Json.bool true) (GParser.string "true")
private def jfalse : GParser conditional Json :=
  GParser.map (fun _ => Json.bool false) (GParser.string "false")

-- Recursive value via `fix` ----------------------------------------------

private def value : GParser conditional Json :=
  GParser.fix fun value =>
    let commaValue : GParser conditional Json :=
      GParser.seqR GParser.ws (GParser.seqR (GParser.ch ',') (GParser.seqR GParser.ws value))
    let arrayBody : GParser flexible (List Json) :=
      GParser.alt
        (GParser.map2 (fun x xs => x :: xs) value (GParser.many commaValue))
        (GParser.pure [])
    let array : GParser conditional Json :=
      GParser.seqR (GParser.ch '[')
        (GParser.seqR GParser.ws
          (GParser.seqL (GParser.map Json.arr arrayBody)
            (GParser.seqR GParser.ws (GParser.ch ']'))))
    let pair : GParser conditional (String × Json) :=
      GParser.map2 (fun k v => (k, v)) jstr
        (GParser.seqR GParser.ws (GParser.seqR (GParser.ch ':') (GParser.seqR GParser.ws value)))
    let commaPair : GParser conditional (String × Json) :=
      GParser.seqR GParser.ws (GParser.seqR (GParser.ch ',') (GParser.seqR GParser.ws pair))
    let objectBody : GParser flexible (List (String × Json)) :=
      GParser.alt
        (GParser.map2 (fun x xs => x :: xs) pair (GParser.many commaPair))
        (GParser.pure [])
    let object : GParser conditional Json :=
      GParser.seqR (GParser.ch '{')
        (GParser.seqR GParser.ws
          (GParser.seqL (GParser.map Json.obj objectBody)
            (GParser.seqR GParser.ws (GParser.ch '}'))))
    -- A byte that starts no value: always fails (the mapped `null` is unreachable).
    let invalid : GParser conditional Json :=
      GParser.map (fun _ => Json.null) (GParser.satisfy (fun _ => false))
    GParser.seqR GParser.ws
      (GParser.dispatch fun b =>
        if b == Ascii.lbrace then object
        else if b == Ascii.lbracket then array
        else if b == Ascii.quote then jstring
        else if b == 116 then jtrue
        else if b == 102 then jfalse
        else if b == 110 then jnull
        else if Ascii.isDigit b || b == Ascii.dash then number
        else invalid)

/-- One complete JSON document: a value, optional trailing whitespace, then EOF (so
trailing garbage is rejected). -/
def parser : GParser conditional Json := GParser.seqL value (GParser.seqR GParser.ws GParser.eof)

/-- Parse a complete JSON document from a `ByteArray`, returning the value or a
positioned `ParseError`. -/
def parse (arr : ByteArray) : Except ParseError Json := parser.parse arr

/-- Parse a complete JSON document from a `String`. -/
def parse! (s : String) : Except ParseError Json := parser.parse s.toUTF8

-- Serialization ----------------------------------------------------------

namespace Json

private def hexDigit (n : Nat) : Char := "0123456789abcdef".toList.getD n '0'

/-- Escape a string body for JSON output: `"`, `\`, and control characters. Non-ASCII is
emitted verbatim (valid UTF-8 JSON). -/
def escape (s : String) : String :=
  -- ponytail: naive `++` append, quadratic in the escaped length; fine for a serializer,
  -- switch to a `String` builder if it ever shows up in a profile.
  s.foldl (fun acc c =>
    acc ++
      (if c == '"' then "\\\""
       else if c == '\\' then "\\\\"
       else if c == '\n' then "\\n"
       else if c == '\t' then "\\t"
       else if c == '\r' then "\\r"
       else if c == Char.ofNat 8 then "\\b"
       else if c == Char.ofNat 12 then "\\f"
       else if c.toNat < 0x20 then
         String.ofList ['\\', 'u', '0', '0', hexDigit (c.toNat / 16), hexDigit (c.toNat % 16)]
       else String.singleton c)) ""

/-- Render an exact `num mantissa exponent` to a decimal literal, inserting the point
`exponent` digits from the right (`num 25 1` → `"2.5"`, `num 5 3` → `"0.005"`). -/
def renderNum (m : Int) (e : Nat) : String :=
  if e == 0 then toString m
  else
    let ds := List.replicate (e + 1 - (toString m.natAbs).length) '0' ++ (toString m.natAbs).toList
    let k := ds.length - e
    (if m < 0 then "-" else "") ++ String.ofList (ds.take k) ++ "." ++ String.ofList (ds.drop k)

/-- Serialize a value to compact RFC-8259 JSON (no insignificant whitespace). Round-trips
through `parse` (the value, not necessarily the mantissa/exponent split). -/
partial def render : Json → String
  | .null       => "null"
  | .bool true  => "true"
  | .bool false => "false"
  | .num m e    => renderNum m e
  | .str s      => "\"" ++ escape s ++ "\""
  | .arr xs     => "[" ++ String.intercalate "," (xs.map render) ++ "]"
  | .obj kvs    => "{" ++ String.intercalate ","
      (kvs.map fun kv => "\"" ++ escape kv.1 ++ "\":" ++ render kv.2) ++ "}"

instance : ToString Json := ⟨render⟩

end Json

end Grip.Json

/-! ### Sanity guards. -/
section
open Grip Grip.Json

#guard (GParser.run? parser "null".toUTF8) == some Json.null
#guard (GParser.run? parser "true".toUTF8) == some (Json.bool true)
#guard (GParser.run? parser "false".toUTF8) == some (Json.bool false)
-- integers are `num n 0`, full bignum precision, signs handled
#guard (GParser.run? parser "42".toUTF8) == some (Json.num 42 0)
#guard (GParser.run? parser "-42".toUTF8) == some (Json.num (-42) 0)
#guard (GParser.run? parser "0".toUTF8) == some (Json.num 0 0)
#guard (GParser.run? parser "123456789012345678901234567890".toUTF8)
        == some (Json.num 123456789012345678901234567890 0)
-- fraction / exponent / signs => exact mantissa * 10^(-exponent), no rounding
#guard (GParser.run? parser "2.5".toUTF8) == some (Json.num 25 1)
#guard (GParser.run? parser "-2.5e3".toUTF8) == some (Json.num (-2500) 0)
#guard (GParser.run? parser "5e-1".toUTF8) == some (Json.num 5 1)
-- `int` smart constructor and strict `int?` extractor
#guard Json.int 42 == Json.num 42 0
#guard (Json.num 42 0).int? == some 42
#guard (Json.num 25 1).int? == none
#guard Json.null.int? == none
-- accessors
#guard (Json.obj [("a", Json.int 1)]).get? "a" == some (Json.int 1)
#guard (Json.obj [("a", Json.int 1)]).get? "b" == none
#guard Json.null.get? "a" == none
#guard (Json.arr [Json.int 1, Json.int 2]).at? 1 == some (Json.int 2)
#guard (Json.arr [Json.int 1]).at? 5 == none
-- strings: escapes and \u decode
#guard (GParser.run? parser "\"a\\nb\"".toUTF8) == some (Json.str "a\nb")
#guard (GParser.run? parser "\"\\u0041\"".toUTF8) == some (Json.str "A")
#guard (GParser.run? parser "\"\\uD834\\uDD1E\"".toUTF8) == some (Json.str "𝄞")
-- containers
#guard (GParser.run? parser "[1,2,3]".toUTF8)
        == some (Json.arr [Json.num 1 0, Json.num 2 0, Json.num 3 0])
#guard (GParser.run? parser "[]".toUTF8) == some (Json.arr [])
#guard (GParser.run? parser "{}".toUTF8) == some (Json.obj [])
#guard (GParser.run? parser "  { \"a\" : true , \"b\" : [1] }  ".toUTF8)
        == some (Json.obj [("a", Json.bool true), ("b", Json.arr [Json.num 1 0])])
-- strict RFC-8259 rejections
#guard (GParser.run? parser "01".toUTF8) == none            -- leading zero
#guard (GParser.run? parser "1.".toUTF8) == none            -- trailing dot
#guard (GParser.run? parser "1e".toUTF8) == none            -- bare exponent
#guard (GParser.run? parser "[1,]".toUTF8) == none          -- trailing comma
#guard (GParser.run? parser "1 2".toUTF8) == none           -- trailing garbage
#guard (GParser.run? parser "\"a\\q\"".toUTF8) == none      -- bad escape

-- serialization: render is compact and round-trips through parse
#guard toString (Json.num 25 1) == "2.5"
#guard toString (Json.num 5 3) == "0.005"
#guard toString (Json.num (-5) 1) == "-0.5"
#guard toString (Json.int 42) == "42"
#guard toString (Json.str "a\nb\"c") == "\"a\\nb\\\"c\""
#guard toString (Json.arr [Json.int 1, Json.int 2]) == "[1,2]"
#guard toString (Json.obj [("a", Json.bool true)]) == "{\"a\":true}"
#guard
  (let v := Json.obj [("a", Json.arr [Json.num 25 1, Json.null]), ("b", Json.str "x\ty")]
   parse! (toString v) == .ok v)

end
