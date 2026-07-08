/-
Copyright 2026 Jonathan Cubides. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grip.Parser

/-!
# Grip.Examples.Yaml -- a flow-style YAML parser

Parses YAML's JSON-compatible *flow* syntax into a tree:

```
<value>  ::= <ws> ( <seq> | <map> | <scalar> )
<seq>    ::= "[" <ws> ( <value> ("," <value>)* )? <ws> "]"
<map>    ::= "{" <ws> ( <pair> ("," <pair>)* )? <ws> "}"
<pair>   ::= <scalar> <ws> ":" <ws> <value>
<scalar> ::= '"' ... '"' | run of non-delimiter bytes
```

Recursion is `GParser.fix`; the leading byte after whitespace selects seq / map /
quoted / plain via `GParser.dispatch`; `capture` reads a scalar's bytes.

(ponytail: block (indentation-based) YAML -- the part that makes YAML YAML -- is
omitted, along with anchors, tags, and multi-document streams. Flow style is the
JSON-superset core and the part a combinator parser handles cleanly.)
-/

namespace Grip.Examples.Yaml

open Grip

/-- A YAML value in the flow-syntax subset. -/
inductive Yaml where
  /-- A scalar (string, number, or bareword -- all kept as text). -/
  | scalar : String → Yaml
  /-- A flow sequence `[a, b, c]`. -/
  | seq : List Yaml → Yaml
  /-- A flow mapping `{k: v, ...}`. -/
  | map : List (String × Yaml) → Yaml
  deriving BEq, Repr

@[inline] private def isWs (b : UInt8) : Bool :=
  b == 32 || b == 10 || b == 9 || b == 13

/-- A plain-scalar byte: visible and not a flow delimiter (`, [ ] { } :` or `"`). -/
@[inline] private def isPlainByte (b : UInt8) : Bool :=
  b > 32 && b != 44 && b != 91 && b != 93 && b != 123 && b != 125 && b != 58 && b != 34

@[inline] private def ws : GParser flexible Nat := GParser.takeWhile isWs

/-- A double-quoted scalar's `String` contents (escape-transparent). -/
@[inline] private def quoted : GParser conditional String :=
  GParser.seqR (GParser.byte 34)
    (GParser.seqL (GParser.capture (GParser.takeWhile (· != 34))) (GParser.byte 34))

/-- A plain (unquoted) scalar's `String`. -/
@[inline] private def plain : GParser conditional String :=
  GParser.capture (GParser.takeWhile1 isPlainByte)

/-- A scalar key/value string: quoted or plain, by first byte. -/
@[inline] private def scalarStr : GParser conditional String :=
  GParser.dispatch fun b => if b == 34 then quoted else plain

/-- Parse one flow-style YAML value. -/
def value : GParser conditional Yaml :=
  GParser.fix fun value =>
    -- sequence: "[" ws ( value ("," value)* )? ws "]"
    let commaValue : GParser conditional Yaml :=
      GParser.seqR ws (GParser.seqR (GParser.byte 44) (GParser.seqR ws value))
    let seqBody : GParser flexible (List Yaml) :=
      GParser.alt
        (GParser.map2 (fun h t => h :: t) value (GParser.many commaValue))
        (GParser.pure [])
    let seq : GParser conditional Yaml :=
      GParser.seqR (GParser.byte 91)
        (GParser.seqR ws
          (GParser.seqL (GParser.map Yaml.seq seqBody) (GParser.seqR ws (GParser.byte 93))))
    -- mapping: "{" ws ( pair ("," pair)* )? ws "}"
    let pair : GParser conditional (String × Yaml) :=
      GParser.map2 (·, ·) scalarStr
        (GParser.seqR ws (GParser.seqR (GParser.byte 58) (GParser.seqR ws value)))
    let commaPair : GParser conditional (String × Yaml) :=
      GParser.seqR ws (GParser.seqR (GParser.byte 44) (GParser.seqR ws pair))
    let mapBody : GParser flexible (List (String × Yaml)) :=
      GParser.alt
        (GParser.map2 (fun h t => h :: t) pair (GParser.many commaPair))
        (GParser.pure [])
    let flowMap : GParser conditional Yaml :=
      GParser.seqR (GParser.byte 123)
        (GParser.seqR ws
          (GParser.seqL (GParser.map Yaml.map mapBody) (GParser.seqR ws (GParser.byte 125))))
    GParser.seqR ws
      (GParser.dispatch fun b =>
        if b == 91 then seq                                     -- '['
        else if b == 123 then flowMap                           -- '{'
        else if b == 34 then GParser.map Yaml.scalar quoted     -- '"'
        else GParser.map Yaml.scalar plain)

/-- Parse one flow-style YAML value from `arr`, or `none` on failure. -/
@[inline] def parse (arr : ByteArray) : Option Yaml := GParser.run? value arr

-- Acceptance guards -------------------------------------------------------

#guard parse "hello".toUTF8 == some (.scalar "hello")
#guard parse "[1, 2, 3]".toUTF8 == some (.seq [.scalar "1", .scalar "2", .scalar "3"])
#guard parse "{a: 1, b: two}".toUTF8
        == some (.map [("a", .scalar "1"), ("b", .scalar "two")])
#guard parse "[]".toUTF8 == some (.seq [])
#guard parse "{}".toUTF8 == some (.map [])
#guard parse "{name: \"grip\", tags: [fast, graded]}".toUTF8
        == some (.map [("name", .scalar "grip"),
                       ("tags", .seq [.scalar "fast", .scalar "graded"])])
#guard parse "[[1, 2], [3, 4]]".toUTF8
        == some (.seq [.seq [.scalar "1", .scalar "2"], .seq [.scalar "3", .scalar "4"]])

end Grip.Examples.Yaml
