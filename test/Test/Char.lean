/-
Copyright (c) 2026 Jonathan Cubides. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Prieto-Cubides
-/
import Grip

/-! Checks for `Grip.Char`, run at elaboration by `lake build Test`. -/

section
open Grip

#guard (GParser.run? GParser.anyChar "aπ".toUTF8) == some 'a'
#guard (GParser.run? (GParser.char 'a') "abc".toUTF8) == some 'a'
#guard (GParser.run? (GParser.char 'x') "abc".toUTF8) == none
-- multibyte: 'π' is 2 UTF-8 bytes (0xCF 0x80); anyChar decodes it as one Char.
#guard (GParser.run? GParser.anyChar "π".toUTF8) == some 'π'
#guard decodeUtf8 (ByteArray.mk #[0xC2, 0x80]) 0 |>.isSome
#guard decodeUtf8 (ByteArray.mk #[0xE0, 0xA0, 0x80]) 0 |>.isSome
#guard decodeUtf8 (ByteArray.mk #[0xF0, 0x90, 0x80, 0x80]) 0 |>.isSome
#guard decodeUtf8 (ByteArray.mk #[0xC0, 0x80]) 0 == none
#guard decodeUtf8 (ByteArray.mk #[0xE0, 0x80, 0x80]) 0 == none
#guard decodeUtf8 (ByteArray.mk #[0xED, 0xA0, 0x80]) 0 == none
#guard decodeUtf8 (ByteArray.mk #[0xF4, 0x90, 0x80, 0x80]) 0 == none
#guard decodeUtf8 (ByteArray.mk #[0xF5, 0x80, 0x80, 0x80]) 0 == none
#guard (GParser.run? (GParser.string "true") "true!".toUTF8) == some ()
#guard (GParser.run? (GParser.string "true") "trur".toUTF8) == none

end
