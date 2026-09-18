/-
Copyright (c) 2026 Jonathan Cubides. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Prieto-Cubides

The grammar and `atom`/`list` structure follow Examples/SExp.lean in
prim-parser by Jan Mas Rovira (https://github.com/janmasrovira/prim-parser,
commit 30d0ad8, 2026-05-08). grip's representation and dispatch differ: a
flat `List Sexp` rather than cons-pairs, and `dispatch` on the leading byte
rather than a backtracking `<|>`.
-/
import Grip

/-!
# Grip.Examples.Sexp -- an S-expression parser built on grip combinators

Parses the classic Lisp surface syntax into a real tree:

```
<sexp>  ::= <ws> ( <atom> | "(" <ws> <sexp>* <ws> ")" )
<atom>  ::= run of non-whitespace, non-parenthesis bytes
```

The recursive `sexp` is `GParser.fix`; the leading byte after whitespace selects atom
vs list via `GParser.dispatch` (one byte read, no failed `alt` attempt); `capture`
turns an atom's byte run into its `String` name; `many` collects list elements. Every
element carries its own trailing whitespace (`seqL sexp ws`), so the closing `)` is
reached with no whitespace left to skip.
-/

namespace Grip.Examples.Sexp

open Grip

/-- An S-expression: an atom (symbol or literal token) or a parenthesised list. -/
inductive Sexp where
  /-- A leaf token, e.g. `+`, `foo`, `42`. -/
  | atom : String → Sexp
  /-- A parenthesised list of sub-expressions. -/
  | list : List Sexp → Sexp
  deriving BEq, Repr

/-- An atom byte: any visible byte that is not a delimiter (`(` or `)`). -/
@[inline] private def isAtomByte (b : UInt8) : Bool :=
  b > Ascii.space && b != Ascii.lparen && b != Ascii.rparen

/-- Parse one S-expression (after any leading whitespace). -/
def sexp : GParser conditional Sexp :=
  GParser.fix fun sexp =>
    let atom : GParser conditional Sexp :=
      Sexp.atom <$> GParser.capture (GParser.takeWhile1 isAtomByte)
    let elements : GParser flexible (List Sexp) :=
      GParser.many (sexp <* GParser.ws)               -- each element eats its trailing ws
    let list : GParser conditional Sexp :=
      GParser.ch '(' *> GParser.ws *>
        ((Sexp.list <$> elements) <* (GParser.ws *> GParser.ch ')'))
    GParser.ws *> GParser.dispatch fun b => if b == Ascii.lparen then list else atom

/-- Parse one S-expression from `arr`, or `none` on failure. -/
@[inline] def parse (arr : ByteArray) : Option Sexp := GParser.run? sexp arr

-- Acceptance guards -------------------------------------------------------

#guard parse "atom".toUTF8 == some (.atom "atom")
#guard parse "(+ 1 2)".toUTF8 == some (.list [.atom "+", .atom "1", .atom "2"])
#guard parse "(a (b c))".toUTF8 == some (.list [.atom "a", .list [.atom "b", .atom "c"]])
#guard parse "()".toUTF8 == some (.list [])
#guard parse "  (lambda (x) x)".toUTF8
        == some (.list [.atom "lambda", .list [.atom "x"], .atom "x"])
#guard parse "(nested (deeply (here)))".toUTF8
        == some (.list [.atom "nested", .list [.atom "deeply", .list [.atom "here"]]])
-- Malformed: bare ')' is not an atom or list.
#guard parse ")".toUTF8 == none

end Grip.Examples.Sexp
