/-
Copyright (c) 2026 Jonathan Cubides. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Cubides
-/

import Grip.Byte
import Grip.Scan
import Grip.Error

/-!
# Grip.Parser: ungraded face for graded parsers

`Parser α` is `GParser fallible α`: the idempotent `fallible` grade satisfies
`Grade.mul fallible fallible = fallible` and `Grade.choice fallible fallible = fallible`
(both verified by `#guard` in `Grip.Grade`), so standard `Monad` and `Alternative`
instances work here with grade tracking disabled.

`GParser.weakenFallible` bridges the precise graded layer: the `CoeOut` instance makes
the coercion transparent, so any `GParser g α` can be used where a `Parser α`
is expected.

## `gdo`: graded do-notation

`gdo` desugars `let x ← p` and bare `p` lines into `GParser.bind`/`GParser.pure`
calls, preserving the exact product grade in the elaborated term instead of
collapsing everything to `fallible`. An optional trailing `grade_by proof` coerces
the elaborated grade to the expected one via `GParser.gcast`.

`gdo` does not yet support `match` expressions inside the block; use explicit
`GParser.bind p fun | .foo => ...` calls in that case.
-/

namespace Grip

/-- The ungraded parser type: `GParser` at the idempotent `fallible` grade
(`errors = possibly`, `consumes = possibly`). Standard `Monad` and `Alternative`
instances work here because `Grade.mul fallible fallible = fallible` definitionally. -/
abbrev Parser (α : Type) := GParser fallible α

/-! ### Monad instance -/

/-- `Monad` instance for `Parser`. `pure` wraps a value with
`GParser.weakenFallible ∘ GParser.pure`; `bind` sequences two `Parser` actions,
weakening the `fallible * fallible` result grade back to `fallible`. -/
instance : Monad Parser where
  pure a   := GParser.weakenFallible (GParser.pure a)
  bind x f := GParser.weakenFallible (GParser.bind x f)

/-! ### Alternative instance -/

/-- `Alternative` instance for `Parser`. `failure` is `GParser.fail` weakened to
`fallible`; `orElse` uses `GParser.alt` and weakens the choice result to `fallible`. -/
instance : Alternative Parser where
  failure   := GParser.weakenFallible GParser.fail
  orElse x y := GParser.weakenFallible (GParser.alt x (y ()))

/-! ### Coercion from precisely-graded parsers -/

/-- Any `GParser g α` coerces silently to `Parser α` via `GParser.weakenFallible`,
so precise graded parsers can be used wherever `Parser` is expected without
explicit casts.

We use `CoeOut` rather than `Coe` because in Lean 4.28 `Coe`'s first parameter is
`semiOutParam`, which would require the grade `g` to be determined from the
destination type alone; impossible when `g` is free. `CoeOut` applies "left-to-right"
(source known → determine destination), which is exactly our direction. -/
instance {g : Grade} {α : Type} : CoeOut (GParser g α) (Parser α) := ⟨GParser.weakenFallible⟩

/-! ### Grade cast helper -/

/-- Cast a parser's grade via an equality proof. Used by the `grade_by` tail of
`gdo` blocks to coerce the elaborated product grade to the expected type. -/
@[inline] def GParser.gcast {g g' : Grade} {α : Type} (h : g = g') (p : GParser g α) :
    GParser g' α :=
  h ▸ p

/-! ### Top-level entry point -/

/-- Run a parser from offset 0, returning a positioned `ParseError` on failure.
Line and column are 1-based byte positions derived by scanning `arr` for newlines. -/
def GParser.parse {g : Grade} {α : Type} (p : GParser g α) (arr : ByteArray) :
    Except ParseError α :=
  match p.run arr 0 with
  | .ok a _  => .ok a
  | .error e => .error (mkParseError arr e)

/-! ### MonadExcept instance -/

/-- `throw` at `fallible` grade: immediately fail with the supplied labels, its
offset set to the current position. -/
def GParser.throwErr {α : Type} (e : Err) : Parser α where
  run := fun _ p => .error { e with pos := p }
  cwit := by intro arr q a q' h; exact absurd h (by simp)
  ewit := by intro _ arr q; exact ⟨{ e with pos := q }, rfl⟩
  swit := by intro he; exact absurd he (by decide)
  bwit := by intro arr q a q' hq h; exact absurd h (by simp)

/-- `tryCatch` at `fallible` grade: run `p`; on success pass through; on failure
call the handler `h` and run its result from the same offset. -/
def GParser.tryCatch {α : Type} (p : Parser α) (h : Err → Parser α) : Parser α where
  run := fun arr q =>
    match p.run arr q with
    | .ok a q' => .ok a q'
    | .error e => (h e).run arr q
  cwit := by
    intro arr q a q' heq
    split at heq
    · rename_i b p' hp
      simp only [ParseResult.ok.injEq] at heq
      obtain ⟨rfl, rfl⟩ := heq
      exact p.cwit hp
    · rename_i e hp
      exact (h e).cwit heq
  ewit := by intro he; exact absurd he (by decide)
  swit := by intro he; exact absurd he (by decide)
  bwit := by
    intro arr q a q' hq heq
    split at heq
    · rename_i b p' hp
      simp only [ParseResult.ok.injEq] at heq
      obtain ⟨rfl, rfl⟩ := heq
      exact p.bwit hq hp
    · rename_i e hp
      exact (h e).bwit hq heq

instance : MonadExcept Err Parser where
  throw e  := GParser.throwErr e
  tryCatch := GParser.tryCatch

end Grip

/-- Trailing element in a `gdo` block: supply an equality proof to coerce the
elaborated grade to the expected type. Example:
```
gdo
  let a ← p
  q a
  grade_by by rfl
``` -/
syntax "grade_by " term : doElem

/-- Graded do-notation over `GParser`: desugars a do-like block into
`GParser.bind`/`GParser.pure` calls, preserving the exact product grade.

Supported forms:
- `let x ← p`: binds `p`'s result via `GParser.bind`
- `let x : T ← p`: same with type annotation
- `let x := e`: local `let`-binding, no parser action
- bare `p` (non-final): sequences via `GParser.bind _ fun _ => ...`
- `return e` (final): wraps `e` in `GParser.pure`
- bare `p` (final): the parser expression itself
- `grade_by proof` (optional final): coerces the elaborated grade via `GParser.gcast`

Example:
```
-- grade is `conditional`, not collapsed to `fallible`
def twoBytes : GParser conditional (UInt8 × UInt8) :=
  gdo
    let a ← GParser.satisfy (fun _ => true)
    let b ← GParser.satisfy (fun _ => true)
    return (a, b)
```

Note: `match` inside `gdo` is not yet supported; use explicit `GParser.bind` with
a lambda instead. -/
syntax (name := gdoNotation) "gdo " doSeq : term

open Lean in
private partial def expandGDoBlock (doSeq : Syntax) : MacroM (TSyntax `term) := do
  -- Use single-backtick name literals to avoid the double-backtick validation
  -- which would fail if `Lean.Parser.Term` isn't in the user's import chain.
  let itemsNode :=
    if doSeq.getKind == `Lean.Parser.Term.doSeqIndent then doSeq[0]
    else doSeq[1]
  let elems := (itemsNode.getArgs.map fun item => item[0]).filter (!·.isMissing)
  if elems.isEmpty then
    Macro.throwError "empty gdo block"
  let (mainElems, castProof) ←
    match elems.back! with
    | `(doElem| grade_by $proof:term) => pure (elems.pop, some proof)
    | _                               => pure (elems, none)
  if mainElems.isEmpty then
    Macro.throwError "empty gdo block (only grade_by)"
  let last := mainElems.back!
  let init := mainElems.pop
  let r ← expandGDoFinal last
  let mut result := r
  for i in List.range init.size |>.reverse do
    result ← expandGDoElem init[i]! result
  match castProof with
  | some proof => `(Grip.GParser.gcast $proof $result)
  | none       => return result
where
  expandGDoElem (elem : Syntax) (rest : TSyntax `term) : MacroM (TSyntax `term) :=
    match elem with
    | `(doElem| let $x:ident ← $e:term)             => `(Grip.GParser.bind $e fun $x => $rest)
    | `(doElem| let _ ← $e:term)                    => `(Grip.GParser.bind $e fun _ => $rest)
    | `(doElem| let $x:ident : $ty:term ← $e:term)  =>
      `(Grip.GParser.bind $e fun ($x : $ty) => $rest)
    | `(doElem| let $x:ident := $e:term)             => `(let $x := $e; $rest)
    | `(doElem| let $x:ident : $ty:term := $e:term) => `(let $x : $ty := $e; $rest)
    | _ =>
      let e : TSyntax `term := ⟨elem.getArgs.back!⟩
      `(Grip.GParser.bind $e fun _ => $rest)
  expandGDoFinal (elem : Syntax) : MacroM (TSyntax `term) := do
    match elem with
    | `(doElem| return $e:term) => `(Grip.GParser.pure $e)
    | `(doElem| return)         => `(Grip.GParser.pure ())
    | _                         => pure ⟨elem.getArgs.back!⟩

open Lean in
@[macro gdoNotation] def expandGDo : Macro := fun stx =>
  expandGDoBlock stx[1]

/-! ### Sanity guards. -/

section Guards
open Grip

-- Coercion: a `conditional` parser coerces to `Parser` via the `CoeOut` instance.
-- The coercion is "source-driven" (left-to-right), so no explicit cast annotation needed.
private def digitP : Parser UInt8 :=
  GParser.satisfy (fun b => 48 ≤ b && b ≤ 57)

example (f : UInt8 → Bool) : Parser UInt8 := GParser.satisfy f

-- `Monad` do-notation collapses grade to `fallible`; `#guard` checks round-trip.
private def twoDigits : Parser (UInt8 × UInt8) := do
  let a ← digitP
  let b ← digitP
  return (a, b)

#guard (GParser.run? twoDigits "57".toUTF8) == some (53, 55)

-- `Alternative`: `<|>` and `failure` work at `Parser`.
private def digitOrFail : Parser UInt8 :=
  digitP <|> failure

#guard (GParser.run? digitOrFail "5".toUTF8) == some 53
#guard (GParser.run? digitOrFail "/".toUTF8) == none

-- `GParser.many` requires `consumes = always`; `conditional` qualifies.
-- Uncommenting the line below would produce a TYPE ERROR (pure has `consumes = never`):
--   #check GParser.many (GParser.pure (0 : Nat))
example : GParser flexible (List UInt8) := GParser.many (GParser.satisfy (· != 0))

-- `gdo`: grade is preserved precisely (stays `conditional`, not collapsed to `fallible`).
-- `conditional * conditional = conditional` because
--   `max always always = always` and `max possibly possibly = possibly` both hold.
private def twoBytes : GParser conditional (UInt8 × UInt8) :=
  gdo
    let a ← GParser.satisfy (fun _ => true)
    let b ← GParser.satisfy (fun _ => true)
    return (a, b)

#guard (GParser.run? twoBytes "AB".toUTF8) == some (65, 66)
#guard (GParser.run? twoBytes "".toUTF8) == none

-- BEq for Except ParseError, needed by the #guard comparisons below.
private instance instBEqExceptPE {β : Type} [BEq β] : BEq (Except ParseError β) where
  beq
    | .error e1, .error e2 => e1 == e2
    | .ok a,     .ok b     => a == b
    | _,         _         => false

-- `GParser.parse` surfaces a `ParseError` with positioned information.
private def digitOrErr : Parser Nat :=
  GParser.weakenFallible (GParser.nat <?> "number")

#guard (digitOrErr.parse "abc".toUTF8
        == (.error { pos := 0, line := 1, col := 1, expected := ["number"] } :
            Except ParseError Nat))
#guard (digitOrErr.parse "42".toUTF8 == (.ok 42 : Except ParseError Nat))

-- `pretty` is the dependency-free plain fallback; rich terminal output lives in
-- `grip-diagnostics` and delegates to `TermColor.Diagnostics`.
private def prettyTest : String :=
  let e : ParseError := { pos := 5, line := 3, col := 2, expected := ["!"] }
  e.pretty "a\nb\n1".toUTF8

#guard prettyTest == "3:2: expected !\n1\n ^"

end Guards
