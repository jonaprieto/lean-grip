/-
Copyright (c) 2026 Jonathan Cubides. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Prieto-Cubides
-/
import Grip

/-! Checks for `Grip.Combinators`, run at elaboration by `lake build Test`. -/

section
open Grip GParser

#guard (run? digit "7".toUTF8) == some 55
#guard (run? digit "x".toUTF8) == none
#guard (run? hexDigit "f".toUTF8) == some 102
#guard (run? (ch '{') "{".toUTF8) == some ()
#guard (run? ws "  \tx".toUTF8) == some 3
#guard (run? ws1 "x".toUTF8) == none
#guard (run? (oneOf [97, 98]) "b".toUTF8) == some 98
#guard (run? (noneOf [97, 98]) "b".toUTF8) == none

#guard (run? (sepBy digit (ch ',')) "1,2,3".toUTF8)
        == some [49, 50, 51]
#guard (run? (sepBy digit (ch ',')) "".toUTF8) == some []
#guard (run? (between (ch '(') (ch ')') digit) "(5)".toUTF8)
        == some 53
#guard (run? (endBy digit (ch ';')) "1;2;".toUTF8) == some [49, 50]
#guard (run? (endBy1 digit (ch ';')) "1;2;".toUTF8) == some [49, 50]
#guard (run? (endBy1 digit (ch ';')) ";".toUTF8) == none
#guard (run? (many1 digit) "123x".toUTF8) == some [49, 50, 51]
#guard (run? (many1 digit) "x".toUTF8) == none
#guard (run? (skipMany digit) "123x".toUTF8) == some 3
#guard (run? (option (65 : UInt8) digit) "x".toUTF8) == some 65
#guard (run? (optional digit) "x".toUTF8) == some none
#guard (run? (notFollowedBy digit) "x".toUTF8) == some ()
#guard (run? (notFollowedBy digit) "5".toUTF8) == none
#guard (run? eof "".toUTF8) == some ()
#guard (run? eof "x".toUTF8) == none
#guard (run? (manyTill letter (ch '.')) "abc.".toUTF8)
        == some [97, 98, 99]
#guard (run? (chooseG (ch 'a') [ch 'b']) "b".toUTF8) == some ()
#guard (run? (choice [weakenFallible (ch 'a'),
                      weakenFallible (ch 'b')]) "b".toUTF8) == some ()
#guard (run? (count 3 (weakenFallible digit)) "123".toUTF8)
        == some [49, 50, 51]

-- notation (graded): <$> <$ <*> *> <* <|>
#guard (run? ((fun _ => (7 : Nat)) <$> digit) "5".toUTF8) == some 7
#guard (run? ((9 : Nat) <$ digit) "5".toUTF8) == some 9
#guard (run? (ch '(' *> digit <* ch ')') "(5)".toUTF8) == some 53
#guard (run? (digit <|> letter) "a".toUTF8) == some 97
#guard (run? ((fun (a : UInt8) (b : UInt8) => (a, b)) <$> digit <*> digit) "78".toUTF8)
        == some (55, 56)

end
