/-
Copyright (c) 2026 Jonathan Cubides. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Prieto-Cubides

Adapted from Examples/Lambda.lean in prim-parser by Jan Mas Rovira
(https://github.com/janmasrovira/prim-parser, commit 30d0ad8, 2026-05-08):
the `Term` inductive (`var`/`lam`/`app`), the grammar decomposition (`fix`
over term; atom = var or parenthesised term; application as a left fold of
atoms; a backslash-lambda rule), and the `takeWhile1 isAlpha` identifier
helper. grip rewrites these onto its byte API -- `dispatch` on the leading
byte instead of `<|>`, and explicit `ws` instead of `lexeme`.
-/
import Grip

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

/-- An identifier (one or more letters), after any leading whitespace. -/
@[inline] private def name : GParser conditional String :=
  GParser.ws *> GParser.capture (GParser.takeWhile1 Ascii.isAlpha)

/-- Parse one lambda term. -/
def term : GParser conditional Term :=
  GParser.fix fun term =>
    let var : GParser conditional Term :=
      Term.var <$> GParser.capture (GParser.takeWhile1 Ascii.isAlpha)
    let paren : GParser conditional Term :=                        -- '(' term ')'
      GParser.ch '(' *> ((GParser.ws *> term) <* (GParser.ws *> GParser.ch ')'))
    let lam : GParser conditional Term :=                          -- '\' var '.' term
      GParser.ch '\\' *>
        (Term.lam <$> name <*> (GParser.ws *> GParser.ch '.' *> GParser.ws *> term))
    let atom : GParser conditional Term :=
      GParser.ws *> GParser.dispatch fun b =>
        if b == Ascii.lparen then paren else if b == Ascii.backslash then lam else var
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
