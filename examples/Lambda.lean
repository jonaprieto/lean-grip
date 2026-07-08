/-
Copyright 2026 Jonathan Cubides. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grip.Parser

/-!
# Grip.Examples.Lambda -- an untyped lambda-calculus parser built on grip combinators

```
<term> ::= <atom>+                        -- application, left-associative
<atom> ::= <var> | "(" <term> ")" | "\" <var> "." <term>
<var>  ::= run of ASCII letters
```

Application binds tighter than nothing and is left-associative: `f x y` parses as
`(f x) y`. A lambda body extends as far right as possible: `\x. f x` is `\x. (f x)`.
The recursion is `GParser.fix`; the byte after whitespace picks the atom shape via
`GParser.dispatch`; a leading atom followed by `many` more atoms is folded with
`Term.app` to get left-associativity.
-/

namespace Grip.Examples.Lambda

open Grip

/-- An untyped lambda term. -/
inductive Term where
  /-- A variable. -/
  | var : String → Term
  /-- An application `f x`. -/
  | app : Term → Term → Term
  /-- An abstraction `\x. body`. -/
  | lam : String → Term → Term
  deriving BEq, Repr

@[inline] private def isWs (b : UInt8) : Bool :=
  b == 32 || b == 10 || b == 9 || b == 13

/-- An identifier byte: an ASCII letter. -/
@[inline] private def isAlpha (b : UInt8) : Bool :=
  (97 ≤ b && b ≤ 122) || (65 ≤ b && b ≤ 90)

@[inline] private def ws : GParser flexible Nat := GParser.takeWhile isWs

/-- An identifier (one or more letters), after any leading whitespace. -/
@[inline] private def name : GParser conditional String :=
  GParser.seqR ws (GParser.capture (GParser.takeWhile1 isAlpha))

/-- Parse one lambda term. -/
def term : GParser conditional Term :=
  GParser.fix fun term =>
    let var : GParser conditional Term :=
      GParser.map Term.var (GParser.capture (GParser.takeWhile1 isAlpha))
    let paren : GParser conditional Term :=
      GParser.seqR (GParser.byte 40)                              -- '('
        (GParser.seqL (GParser.seqR ws term) (GParser.seqR ws (GParser.byte 41)))  -- ')'
    let lam : GParser conditional Term :=
      GParser.seqR (GParser.byte 92)                              -- '\'
        (GParser.map2 Term.lam name
          (GParser.seqR ws (GParser.seqR (GParser.byte 46)        -- '.'
            (GParser.seqR ws term))))
    let atom : GParser conditional Term :=
      GParser.seqR ws
        (GParser.dispatch fun b =>
          if b == 40 then paren else if b == 92 then lam else var)
    -- Left-associative application: fold trailing atoms onto the first with `Term.app`.
    GParser.map2 (fun first rest => rest.foldl Term.app first) atom (GParser.many atom)

/-- Parse one lambda term from `arr`, or `none` on failure. -/
@[inline] def parse (arr : ByteArray) : Option Term := GParser.run? term arr

-- Acceptance guards -------------------------------------------------------

#guard parse "x".toUTF8 == some (.var "x")
#guard parse "f x".toUTF8 == some (.app (.var "f") (.var "x"))
#guard parse "f x y".toUTF8 == some (.app (.app (.var "f") (.var "x")) (.var "y"))
#guard parse "\\x. x".toUTF8 == some (.lam "x" (.var "x"))
#guard parse "\\x. \\y. x".toUTF8 == some (.lam "x" (.lam "y" (.var "x")))
#guard parse "(\\f. f) x".toUTF8 == some (.app (.lam "f" (.var "f")) (.var "x"))
#guard parse "\\x. f x".toUTF8 == some (.lam "x" (.app (.var "f") (.var "x")))
-- Malformed: a bare lambda with no body.
#guard parse "\\x.".toUTF8 == none

end Grip.Examples.Lambda
