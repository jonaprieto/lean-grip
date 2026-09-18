/-
Copyright (c) 2026 Jonathan Cubides. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Prieto-Cubides
-/
import Grip

/-!
# Grip.Examples.Toml -- a TOML parser (tables, arrays, comments)

Parses a real TOML document -- enough to read a `Cargo.lock` -- into a tree:

```
<doc>    ::= <tws> <entry>* <table>*
<table>  ::= <header> <tws> <entry>*
<header> ::= "[" <key> "]" | "[[" <key> "]]"
<entry>  ::= <key> <tws> "=" <tws> <value>
<value>  ::= <string> | <bool> | <integer> | <array>
<array>  ::= "[" ( <value> <tws> ","? <tws> )* "]"
<tws>    ::= runs of whitespace and "#"-to-end-of-line comments
```

`value` is `GParser.fix` (arrays nest); the first byte after whitespace selects the value
shape via `GParser.dispatch`; `#` comments are skipped as whitespace; `[table]` and
`[[array-of-tables]]` headers start sections; arrays accept a trailing comma and newlines
between elements.

(ponytail: floats, datetimes, inline tables `{ }`, dotted-key assignment, and string
escapes are out of scope -- `Cargo.lock` uses none of them. Add them when a config does.)
-/

namespace Grip.Examples.Toml

open Grip

/-- A TOML value (the subset this parser covers). -/
inductive Value where
  /-- A double-quoted string (no escapes). -/
  | str : String → Value
  /-- A signed integer. -/
  | int : Int → Value
  /-- A boolean. -/
  | bool : Bool → Value
  /-- An array of values. -/
  | array : List Value → Value
  deriving BEq, Repr

/-- A `key = value` assignment. -/
abbrev Entry := String × Value

/-- A `[header]` (or `[[header]]` array-of-tables) section with its entries. -/
structure Table where
  /-- The bracketed header key, e.g. `package` or `a.b`. -/
  header : String
  /-- `true` for `[[header]]` (an array-of-tables element), `false` for `[header]`. -/
  arrayElem : Bool
  /-- The `key = value` entries under this header. -/
  entries : List Entry
  deriving BEq, Repr

/-- A document: top-level entries before any header, then the tables. -/
structure Document where
  /-- Entries before the first `[header]`. -/
  root : List Entry
  /-- The `[header]` / `[[header]]` sections in order. -/
  tables : List Table
  deriving BEq, Repr

/-- A bare-key byte: letter, digit, underscore, or dash. -/
@[inline] private def isKeyByte (b : UInt8) : Bool :=
  Ascii.isAlpha b || Ascii.isDigit b || b == 95 || b == Ascii.dash

/-- A header-key byte: a bare-key byte or a dot (for dotted headers like `a.b`). -/
@[inline] private def isHeaderByte (b : UInt8) : Bool :=
  isKeyByte b || b == Ascii.dot

/-- An integer byte: digit or sign. -/
@[inline] private def isIntByte (b : UInt8) : Bool :=
  Ascii.isDigit b || b == Ascii.dash || b == Ascii.plus

/-- One unit of skippable text: a single whitespace byte, or a whole `#`-comment (from
`#` to just before the newline). Always consumes on success, so it drives `skipMany`. -/
private def wsOrComment : GParser conditional Unit :=
  GParser.dispatch fun b =>
    if b == Ascii.hash then
      (fun _ => ()) <$> (GParser.byte Ascii.hash *> GParser.takeWhile (· != Ascii.lf))
    else
      (fun _ => ()) <$> GParser.satisfy Ascii.isWs

/-- Skip whitespace and comments. -/
private def tws : GParser flexible Nat := GParser.skipMany wsOrComment

/-- A TOML value: string, array, bool, or integer, chosen by first byte. Recursive
because an array holds values. -/
private def value : GParser conditional Value :=
  GParser.fix fun value =>
    let strVal : GParser conditional Value :=
      Value.str <$>
        (GParser.byte Ascii.quote *> GParser.capture (GParser.takeWhile (· != Ascii.quote))
          <* GParser.byte Ascii.quote)
    -- Accept only an exact `true`/`false`; a bareword like `trueish` must fail.
    let boolVal : GParser conditional Value :=
      GParser.bind (GParser.capture (GParser.takeWhile1 Ascii.isAlpha)) fun s =>
        if s == "true" then GParser.weakenFallible (GParser.pure (Value.bool true))
        else if s == "false" then GParser.weakenFallible (GParser.pure (Value.bool false))
        else GParser.weakenFallible (GParser.fail : GParser empty Value)
    -- Accept only a token that parses as an integer; `+` or `--7` must fail.
    let intVal : GParser conditional Value :=
      GParser.bind (GParser.capture (GParser.takeWhile1 isIntByte)) fun s =>
        match s.toInt? with
        | some n => GParser.weakenFallible (GParser.pure (Value.int n))
        | none   => GParser.weakenFallible (GParser.fail : GParser empty Value)
    -- One array element: a value, then optional whitespace / trailing comma / whitespace.
    let elem : GParser conditional Value :=
      value <* tws <* GParser.optional (GParser.byte Ascii.comma) <* tws
    let arrVal : GParser conditional Value :=
      Value.array <$>
        (GParser.byte Ascii.lbracket *> tws *> GParser.many elem
          <* tws <* GParser.byte Ascii.rbracket)
    -- Unknown first byte: fail without consuming (so the enclosing `many` stops at `]`).
    let noValue : GParser conditional Value :=
      (fun _ => Value.int 0) <$> GParser.satisfy (fun _ => false)
    GParser.dispatch fun b =>
      if b == Ascii.quote then strVal
      else if b == Ascii.lbracket then arrVal
      else if b == Ascii.code 't' || b == Ascii.code 'f' then boolVal
      else if isIntByte b then intVal
      else noValue

/-- One `key = value` entry. -/
private def entry : GParser conditional Entry :=
  GParser.map2 (·, ·)
    (GParser.capture (GParser.takeWhile1 isKeyByte))
    (tws *> GParser.byte Ascii.equals *> tws *> value)

/-- A `[header]` or `[[header]]` line; returns the header key and whether it is an
array-of-tables element. -/
private def tableHeader : GParser conditional (String × Bool) :=
  GParser.byte Ascii.lbracket *>
    GParser.dispatch fun b =>
      if b == Ascii.lbracket then
        (·, true) <$>
          (GParser.byte Ascii.lbracket *> GParser.capture (GParser.takeWhile1 isHeaderByte)
            <* GParser.byte Ascii.rbracket <* GParser.byte Ascii.rbracket)
      else
        (·, false) <$>
          (GParser.capture (GParser.takeWhile1 isHeaderByte) <* GParser.byte Ascii.rbracket)

/-- One `[header]` section and its entries. -/
private def table : GParser conditional Table :=
  GParser.map2 (fun (h, arr) ents => ⟨h, arr, ents⟩)
    tableHeader
    (tws *> GParser.many (entry <* tws))

/-- Parse a whole TOML document. -/
def document : GParser flexible Document :=
  tws *> GParser.map2 (fun root tables => ⟨root, tables⟩)
    (GParser.many (entry <* tws))
    (GParser.many (table <* tws))

/-- Parse a TOML document from `arr`, or `none` on failure. -/
@[inline] def parse (arr : ByteArray) : Option Document :=
  GParser.run? document arr

-- Acceptance guards -------------------------------------------------------

/-- Convenience: a document with only root entries. -/
private def rootDoc (es : List Entry) : Document := ⟨es, []⟩

#guard parse "name = \"grip\"".toUTF8 == some (rootDoc [("name", .str "grip")])
#guard parse "count = 42".toUTF8 == some (rootDoc [("count", .int 42)])
#guard parse "delta = -7".toUTF8 == some (rootDoc [("delta", .int (-7))])
#guard parse "enabled = true".toUTF8 == some (rootDoc [("enabled", .bool true)])
#guard parse "  spaced   =   99  ".toUTF8 == some (rootDoc [("spaced", .int 99)])
#guard parse "".toUTF8 == some (rootDoc [])
-- Comments are skipped like whitespace.
#guard parse "# a comment\nx = 1\n# trailing\n".toUTF8 == some (rootDoc [("x", .int 1)])
-- A bareword that is not exactly `true`/`false` fails the value.
#guard parse "enabled = trueish".toUTF8 == some (rootDoc [])
-- Arrays, including a trailing comma and newlines.
#guard parse "deps = [\"a\", \"b\"]".toUTF8
        == some (rootDoc [("deps", .array [.str "a", .str "b"])])
#guard parse "deps = [\n \"a\",\n \"b\",\n]".toUTF8
        == some (rootDoc [("deps", .array [.str "a", .str "b"])])
#guard parse "empty = []".toUTF8 == some (rootDoc [("empty", .array [])])
-- A single `[table]`.
#guard parse "[owner]\nname = \"x\"\n".toUTF8
        == some ⟨[], [⟨"owner", false, [("name", .str "x")]⟩]⟩
-- An array-of-tables `[[package]]`, the Cargo.lock shape.
#guard parse "version = 3\n\n[[package]]\nname = \"adler\"\nversion = \"2.0\"\n".toUTF8
        == some ⟨[("version", .int 3)],
                 [⟨"package", true, [("name", .str "adler"), ("version", .str "2.0")]⟩]⟩

end Grip.Examples.Toml
