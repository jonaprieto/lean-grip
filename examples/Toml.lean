/-
Copyright 2026 Jonathan Cubides. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grip

/-!
# Grip.Examples.Toml -- a minimal TOML key/value parser

Parses top-level `key = value` entries into an association list:

```
<toml>  ::= ( <ws> <entry> )* <ws>
<entry> ::= <key> <ws> "=" <ws> <value>
<value> ::= <string> | <bool> | <integer>
```

Values cover the three most common scalar shapes: double-quoted strings, `true`/`false`,
and signed integers. The value shape is chosen by its first byte with `GParser.dispatch`.

(ponytail: this is the useful 80% -- `[tables]`, arrays, floats, datetimes, and `#`
comments are omitted. Newlines are treated as ordinary separators. Add the rest when a
config actually needs it.)
-/

namespace Grip.Examples.Toml

open Grip

/-- A TOML scalar value (the subset this parser covers). -/
inductive Value where
  /-- A double-quoted string. -/
  | str : String → Value
  /-- A signed integer. -/
  | int : Int → Value
  /-- A boolean. -/
  | bool : Bool → Value
  deriving BEq, Repr

/-- A bare-key byte: letter, digit, underscore, or dash. -/
@[inline] private def isKeyByte (b : UInt8) : Bool :=
  Ascii.isAlpha b || Ascii.isDigit b || b == 95 || b == Ascii.dash

/-- An integer byte: digit or sign. -/
@[inline] private def isIntByte (b : UInt8) : Bool :=
  Ascii.isDigit b || b == Ascii.dash || b == Ascii.plus

/-- A scalar value, chosen by its first byte. -/
private def value : GParser conditional Value :=
  let strVal : GParser conditional Value :=
    GParser.seqR (GParser.byte Ascii.quote)                    -- opening '"'
      (GParser.seqL (GParser.map Value.str (GParser.capture (GParser.takeWhile (· != Ascii.quote))))
        (GParser.byte Ascii.quote))                            -- closing '"'
  -- Capture the token, then accept only an exact `true`/`false` -- a bareword like
  -- `trueish` must fail, not silently read as `false`.
  let boolVal : GParser conditional Value :=
    GParser.bind (GParser.capture (GParser.takeWhile1 Ascii.isAlpha)) fun s =>
      if s == "true" then GParser.weakenFallible (GParser.pure (Value.bool true))
      else if s == "false" then GParser.weakenFallible (GParser.pure (Value.bool false))
      else GParser.weakenFallible (GParser.fail : GParser empty Value)
  -- Accept only a token that actually parses as an integer; `+` or `--7` must fail
  -- rather than fall back to `0`.
  let intVal : GParser conditional Value :=
    GParser.bind (GParser.capture (GParser.takeWhile1 isIntByte)) fun s =>
      match s.toInt? with
      | some n => GParser.weakenFallible (GParser.pure (Value.int n))
      | none   => GParser.weakenFallible (GParser.fail : GParser empty Value)
  GParser.dispatch fun b =>
    if b == Ascii.quote then strVal
    else if b == Ascii.code 't' || b == Ascii.code 'f' then boolVal   -- 't'rue / 'f'alse
    else intVal

/-- One `key = value` entry. -/
private def entry : GParser conditional (String × Value) :=
  GParser.map2 (·, ·)
    (GParser.capture (GParser.takeWhile1 isKeyByte))
    (GParser.seqR GParser.ws (GParser.seqR (GParser.byte Ascii.equals) (GParser.seqR GParser.ws value)))

/-- Parse a whole document into an ordered association list. -/
def toml : GParser flexible (List (String × Value)) :=
  GParser.seqL (GParser.many (GParser.seqR GParser.ws entry)) GParser.ws

/-- Parse a TOML document from `arr`, or `none` on failure. -/
@[inline] def parse (arr : ByteArray) : Option (List (String × Value)) :=
  GParser.run? toml arr

-- Acceptance guards -------------------------------------------------------

#guard parse "name = \"grip\"".toUTF8 == some [("name", .str "grip")]
#guard parse "count = 42".toUTF8 == some [("count", .int 42)]
#guard parse "delta = -7".toUTF8 == some [("delta", .int (-7))]
#guard parse "enabled = true".toUTF8 == some [("enabled", .bool true)]
#guard parse "off = false".toUTF8 == some [("off", .bool false)]
#guard parse "a = 1\nb = \"two\"\nc = false\n".toUTF8
        == some [("a", .int 1), ("b", .str "two"), ("c", .bool false)]
#guard parse "  spaced   =   99  ".toUTF8 == some [("spaced", .int 99)]
#guard parse "".toUTF8 == some []
-- A bareword that is not exactly `true`/`false` fails the value (it is not misread as
-- `false`); the entry is rejected, so no entry is produced.
#guard parse "enabled = trueish".toUTF8 == some []
#guard parse "on = tru".toUTF8 == some []
-- A sign with no digits is not a valid integer (it is not misread as `0`).
#guard parse "n = +".toUTF8 == some []

end Grip.Examples.Toml
