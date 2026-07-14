/-
Copyright (c) 2026 Jonathan Cubides. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Cubides
-/

/-!
# Grip.Error: parse error payload and pretty-printer

`Err` is the error value carried by the core parser on failure.  It records the
furthest byte offset reached and the set of labels that were expected there.

`ParseError` is the user-facing error produced by `GParser.parse`; it adds
1-based `line` and `col` computed from the source bytes.

Nothing in this file imports from `Grip`; only core Lean / Batteries.
-/

namespace Grip

/-- The error value carried inside the core `Except Err` result.

`pos` is the furthest byte offset any attempted branch reached during parsing.
`expected` is the list of labels attached (via `label`/`<?>`) to the parsers
that failed at `pos`; it is used to compose "expected a or b" messages. -/
structure Err where
  /-- Furthest byte offset reached at failure. -/
  pos      : Nat
  /-- Labels expected at `pos` (one per `label`/`<?>` annotation). -/
  expected : List String
  deriving Repr, DecidableEq, BEq, Inhabited

/-- The result of running a parser at an offset: `ok value newOffset` or `error` with the
furthest failure. One constructor holds the value and the new offset inline, so a
successful step allocates a single object rather than an `Except.ok` wrapping a `Prod`
(the representation `Except Err (α × Nat)` used before). -/
inductive ParseResult (α : Type) where
  /-- Success: the parsed `value` and the `newOffset` reached. -/
  | ok : (value : α) → (newOffset : Nat) → ParseResult α
  /-- Failure carrying the furthest-failure `Err`. -/
  | error : Err → ParseResult α

instance {α : Type} : Inhabited (ParseResult α) := ⟨.error default⟩

/-- User-facing positioned parse error, produced by `GParser.parse`. -/
structure ParseError where
  /-- Byte offset of the failure. -/
  pos      : Nat
  /-- 1-based line number (newline = 0x0a). -/
  line     : Nat
  /-- 1-based byte column (not grapheme column). -/
  col      : Nat
  /-- Labels collected at the failure position. -/
  expected : List String
  deriving Repr, DecidableEq, BEq

/-- Compose a human-readable message from an expected-label list.
Returns "expected a or b" when labels are present, or "unexpected input" when
the list is empty. -/
def ParseError.message (e : ParseError) : String :=
  match e.expected with
  | []  => "unexpected input"
  | [x] => "expected " ++ x
  | xs  => String.intercalate " or " (xs.map ("expected " ++ ·))

/-- `lineColLoop arr safePos i lineStart line` counts 0x0a bytes in
`arr[i : safePos]` and returns `(lineNumber, colNumber)`, both 1-based.
Terminates because `safePos - i` strictly decreases each step. -/
private def lineColLoop (arr : ByteArray) (safePos : Nat) :
    (i lineStart line : Nat) → Nat × Nat
  | i, lineStart, line =>
    if i >= safePos then
      (line, safePos - lineStart + 1)
    else if arr[i]! == 0x0a then
      lineColLoop arr safePos (i + 1) (i + 1) (line + 1)
    else
      lineColLoop arr safePos (i + 1) lineStart line
termination_by i _ _ => safePos - i

/-- Compute 1-based `(line, col)` for byte offset `pos` in `arr`.
Line is the count of 0x0a bytes in `arr[0:pos]` plus one.
Col is `pos` minus the index just after the last 0x0a before `pos`, plus one. -/
private def lineColOf (arr : ByteArray) (pos : Nat) : Nat × Nat :=
  lineColLoop arr (min pos arr.size) 0 0 1

/-- Find the byte index of the start of the line containing `pos`: the position
just after the last 0x0a strictly before `pos`, or 0 if none.
`go i` scans backwards from `i` to 0. -/
private def lineStartOf (arr : ByteArray) (pos : Nat) : Nat :=
  let safePos := min pos arr.size
  let rec go : Nat → Nat
    | 0     => 0
    | i + 1 => if arr[i]! == 0x0a then i + 1 else go i
  go safePos

/-- Find the byte index of the end of the line containing `pos`: the first 0x0a
at or after `pos`, or `arr.size` if none. -/
private def lineEndOf (arr : ByteArray) (pos : Nat) : Nat :=
  let safePos := min pos arr.size
  let rec go (i : Nat) : Nat :=
    if i >= arr.size then arr.size
    else if arr[i]! == 0x0a then i
    else go (i + 1)
  termination_by arr.size - i
  go safePos

/-- Extract the source line containing byte offset `pos` as a `String`.
Returns an empty string when UTF-8 decoding fails. -/
private def sourceLine (arr : ByteArray) (pos : Nat) : String :=
  let s := lineStartOf arr pos
  let e := lineEndOf arr pos
  match String.fromUTF8? (arr.extract s e) with
  | some str => str
  | none     => ""

/-- Build a `ParseError` from a raw `Err` and the source `ByteArray`. -/
def mkParseError (arr : ByteArray) (e : Err) : ParseError :=
  let (line, col) := lineColOf arr e.pos
  { pos := e.pos, line := line, col := col, expected := e.expected }

/-- Render the error as `line:col: message`, followed by the offending source
line and a caret (`^`) under the failing column. -/
def ParseError.pretty (e : ParseError) (src : ByteArray) : String :=
  let msg     := e.message
  let srcLine := sourceLine src e.pos
  let caret   := String.ofList (List.replicate (e.col - 1) ' ') ++ "^"
  s!"{e.line}:{e.col}: {msg}\n{srcLine}\n{caret}"

end Grip
