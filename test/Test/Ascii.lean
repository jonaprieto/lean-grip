/-
Copyright (c) 2026 Jonathan Cubides. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Prieto-Cubides
-/
import Grip

/-! Checks for `Grip.Ascii`, run at elaboration by `lake build Test`. -/

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
