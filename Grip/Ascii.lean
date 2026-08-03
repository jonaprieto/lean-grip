/-
Copyright (c) 2026 Jonathan Cubides. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Prieto-Cubides
-/

/-!
# Grip.Ascii: named ASCII byte predicates, constants, and helpers

Pure byte layer: `is`-prefixed predicates over `UInt8`, the common delimiter bytes as
named constants, and `code : Char → UInt8` for ASCII character literals. No parsers and
no grades live here; `Grip.Combinators` builds parsers on top. Batteries-only.
-/

namespace Grip.Ascii

/-- Whitespace: the union of space (0x20), line feed (0x0A), tab (0x09), and carriage
return (0x0D). Use the named constants `space`/`lf`/`tab`/`cr` (below) to match one
specific whitespace byte, or `isBlank` for just space and tab. -/
@[inline] def isWs (b : UInt8) : Bool := b == 32 || b == 10 || b == 9 || b == 13
/-- Blank: space (0x20) or tab (0x09) only, excluding line breaks. -/
@[inline] def isBlank (b : UInt8) : Bool := b == 32 || b == 9
/-- Decimal digit `0`-`9`. -/
@[inline] def isDigit (b : UInt8) : Bool := 48 ≤ b && b ≤ 57
/-- Nonzero decimal digit `1`-`9`. -/
@[inline] def isDigit19 (b : UInt8) : Bool := 49 ≤ b && b ≤ 57
/-- Uppercase ASCII letter `A`-`Z`. -/
@[inline] def isUpper (b : UInt8) : Bool := 65 ≤ b && b ≤ 90
/-- Lowercase ASCII letter `a`-`z`. -/
@[inline] def isLower (b : UInt8) : Bool := 97 ≤ b && b ≤ 122
/-- ASCII letter. -/
@[inline] def isAlpha (b : UInt8) : Bool := isUpper b || isLower b
/-- ASCII letter or decimal digit. -/
@[inline] def isAlphaNum (b : UInt8) : Bool := isAlpha b || isDigit b
/-- Hexadecimal digit `0`-`9`, `a`-`f`, `A`-`F`. -/
@[inline] def isHexDigit (b : UInt8) : Bool :=
  isDigit b || (97 ≤ b && b ≤ 102) || (65 ≤ b && b ≤ 70)
/-- Octal digit `0`-`7`. -/
@[inline] def isOctDigit (b : UInt8) : Bool := 48 ≤ b && b ≤ 55
/-- Exponent marker `e` or `E`. -/
@[inline] def isExp (b : UInt8) : Bool := b == 101 || b == 69
/-- Sign byte `+` or `-`. -/
@[inline] def isSign (b : UInt8) : Bool := b == 43 || b == 45
/-- Control byte: `0x00`-`0x1F` or `0x7F` (DEL). -/
@[inline] def isControl (b : UInt8) : Bool := b ≤ 31 || b == 127
/-- Printable ASCII: space through `~`. -/
@[inline] def isPrint (b : UInt8) : Bool := 32 ≤ b && b ≤ 126
/-- Punctuation: printable, not alphanumeric, not space. -/
@[inline] def isPunct (b : UInt8) : Bool := isPrint b && !isAlphaNum b && b != 32

/-- Numeric value of a decimal digit byte (meaningful only when `isDigit`). -/
@[inline] def digitValue (b : UInt8) : Nat := b.toNat - 48
/-- Numeric value of a hex digit byte (0-15); `0` for non-hex bytes. -/
@[inline] def hexValue (b : UInt8) : Nat :=
  if isDigit b then b.toNat - 48
  else if 97 ≤ b && b ≤ 102 then b.toNat - 87
  else if 65 ≤ b && b ≤ 70 then b.toNat - 55
  else 0

/-- The low byte of a `Char`; ASCII-exact for `c.toNat < 128`. -/
@[inline] def code (c : Char) : UInt8 := UInt8.ofNat c.toNat

/-- Space. -/
@[inline] def space : UInt8 := 32
/-- Horizontal tab. -/
@[inline] def tab : UInt8 := 9
/-- Line feed. -/
@[inline] def lf : UInt8 := 10
/-- Carriage return. -/
@[inline] def cr : UInt8 := 13
/-- Double quote `"`. -/
@[inline] def quote : UInt8 := 34
/-- Apostrophe `'`. -/
@[inline] def apostrophe : UInt8 := 39
/-- Backslash `\`. -/
@[inline] def backslash : UInt8 := 92
/-- Forward slash `/`. -/
@[inline] def slash : UInt8 := 47
/-- Comma `,`. -/
@[inline] def comma : UInt8 := 44
/-- Dot `.`. -/
@[inline] def dot : UInt8 := 46
/-- Colon `:`. -/
@[inline] def colon : UInt8 := 58
/-- Semicolon `;`. -/
@[inline] def semicolon : UInt8 := 59
/-- Hyphen-minus `-`. -/
@[inline] def dash : UInt8 := 45
/-- Plus `+`. -/
@[inline] def plus : UInt8 := 43
/-- Equals `=`. -/
@[inline] def equals : UInt8 := 61
/-- Asterisk `*`. -/
@[inline] def star : UInt8 := 42
/-- Hash `#`. -/
@[inline] def hash : UInt8 := 35
/-- At sign `@`. -/
@[inline] def atSign : UInt8 := 64
/-- Left parenthesis `(`. -/
@[inline] def lparen : UInt8 := 40
/-- Right parenthesis `)`. -/
@[inline] def rparen : UInt8 := 41
/-- Left bracket `[`. -/
@[inline] def lbracket : UInt8 := 91
/-- Right bracket `]`. -/
@[inline] def rbracket : UInt8 := 93
/-- Left brace `{`. -/
@[inline] def lbrace : UInt8 := 123
/-- Right brace `}`. -/
@[inline] def rbrace : UInt8 := 125

end Grip.Ascii

/-! ### Sanity guards. -/
section
open Grip.Ascii

#guard (isWs 32 && isWs 10 && isWs 9 && isWs 13) == true
#guard isWs 65 == false
#guard (isDigit 47 == false) && (isDigit 48 == true)
#guard (isDigit 57 == true) && (isDigit 58 == false)
#guard (isDigit19 48 == false) && (isDigit19 49 == true) && (isDigit19 57 == true)
#guard (isExp 101 && isExp 69 && !isExp 100) == true
#guard (isSign 43 && isSign 45 && !isSign 42) == true
#guard (isHexDigit 0x39 && isHexDigit 0x61 && isHexDigit 0x46) == true
#guard isHexDigit 0x67 == false
#guard (isAlpha 65 && isAlpha 122 && isAlphaNum 48) == true
#guard (isUpper 65 && !isUpper 97 && isLower 97) == true
#guard (isControl 0 && isControl 127 && !isControl 65) == true
#guard (isPrint 32 && isPrint 126 && !isPrint 127) == true
#guard (isPunct 44 && !isPunct 65 && !isPunct 32) == true
#guard digitValue 0x37 == 7
#guard (hexValue 0x41 == 10) && (hexValue 0x66 == 15) && (hexValue 0x39 == 9)
#guard code '{' == 123
#guard (quote == 34) && (comma == 44) && (lbrace == 123) && (colon == 58)

end
