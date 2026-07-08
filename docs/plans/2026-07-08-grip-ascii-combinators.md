# Grip.Ascii + Grip.Combinators Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Give grip a named byte/ASCII layer (`Grip.Ascii`) and a megaparsec-style combinator vocabulary (`Grip.Combinators`), batteries-only, and refactor the six example parsers to use them.

**Architecture:** Two new modules under `Grip/`, both batteries-only, both re-exported by the `Grip` umbrella (which must also start re-exporting `Grip.Char`). `Grip.Ascii` is pure (`UInt8 → Bool` predicates, `UInt8` constants, `Char → UInt8`). `Grip.Combinators` imports `Grip.Ascii` and `Grip.Parser` and builds ready-made byte parsers plus higher-order combinators on the existing core.

**Tech Stack:** Lean 4 (`leanprover/lean4:v4.28.0`), Lake, batteries. Tests are co-located `#guard`s that run at elaboration; the "test runner" is `lake build <target>` (a false `#guard` or missing def is a build error). No test framework.

## Global Constraints

- Batteries-only: neither new module may import mathlib or anything outside core Lean + batteries.
- `autoImplicit` is off (`lakefile.toml`): every type variable must be explicitly bound (`{α : Type}`).
- No `sorry`, no `unsafe`, no `native_decide`.
- Predicate names are `is`-prefixed free functions returning `UInt8 → Bool`, all `@[inline]`.
- Every public definition gets at least one co-located `#guard`.
- The `core` CI job builds `Grip Test Examples`; keep all three green.
- JSON is the headline benchmark (~34ms). Keep its `dispatch`/`foldMany` fast path unless the combinator rewrite stays within 15% (<= ~39ms), measured by `lake exe bench`.
- Combinators that build on `many`/`foldMany` require an always-consuming element (grade `⟨_, always⟩`); respect that in every signature.

---

## File Structure

- Create `Grip/Ascii.lean` -- pure predicates, value helpers, byte constants, `code`.
- Create `Grip/Combinators.lean` -- byte parsers + higher-order combinators.
- Modify `Grip.lean` -- re-export `Grip.Char`, `Grip.Ascii`, `Grip.Combinators`.
- Modify `examples/{Json,Sexp,Lambda,Http,Toml,Yaml}.lean` -- use the new names.
- `lakefile.toml` -- no change (`globs = ["Grip", "Grip.+"]` already covers new modules).

---

## Task 1: `Grip.Ascii` module

**Files:**
- Create: `Grip/Ascii.lean`
- Modify: `Grip.lean`

**Interfaces:**
- Produces: `Grip.Ascii.isWs isBlank isDigit isHexDigit isOctDigit isUpper isLower isAlpha isAlphaNum isControl isPrint isPunct : UInt8 → Bool`; `Grip.Ascii.digitValue hexValue : UInt8 → Nat`; `Grip.Ascii.code : Char → UInt8`; byte constants `Grip.Ascii.{space tab lf cr quote apostrophe backslash slash comma dot colon semicolon dash plus equals star hash at lparen rparen lbracket rbracket lbrace rbrace} : UInt8`.

- [ ] **Step 1: Create `Grip/Ascii.lean` with the predicates, helpers, and constants**

```lean
/-
Copyright 2026 Jonathan Cubides. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Grip.Ascii -- named ASCII byte predicates, constants, and helpers

Pure byte layer: `is`-prefixed predicates over `UInt8`, the common delimiter bytes as
named constants, and `code : Char → UInt8` for ASCII character literals. No parsers and
no grades live here; `Grip.Combinators` builds parsers on top. Batteries-only.
-/

namespace Grip.Ascii

/-- Whitespace: space, line feed, tab, carriage return. -/
@[inline] def isWs (b : UInt8) : Bool := b == 32 || b == 10 || b == 9 || b == 13
/-- Blank: space or tab. -/
@[inline] def isBlank (b : UInt8) : Bool := b == 32 || b == 9
/-- Decimal digit `0`-`9`. -/
@[inline] def isDigit (b : UInt8) : Bool := 48 ≤ b && b ≤ 57
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

/-- Common delimiter bytes, named. -/
@[inline] def space : UInt8 := 32
@[inline] def tab : UInt8 := 9
@[inline] def lf : UInt8 := 10
@[inline] def cr : UInt8 := 13
@[inline] def quote : UInt8 := 34
@[inline] def apostrophe : UInt8 := 39
@[inline] def backslash : UInt8 := 92
@[inline] def slash : UInt8 := 47
@[inline] def comma : UInt8 := 44
@[inline] def dot : UInt8 := 46
@[inline] def colon : UInt8 := 58
@[inline] def semicolon : UInt8 := 59
@[inline] def dash : UInt8 := 45
@[inline] def plus : UInt8 := 43
@[inline] def equals : UInt8 := 61
@[inline] def star : UInt8 := 42
@[inline] def hash : UInt8 := 35
@[inline] def at : UInt8 := 64
@[inline] def lparen : UInt8 := 40
@[inline] def rparen : UInt8 := 41
@[inline] def lbracket : UInt8 := 91
@[inline] def rbracket : UInt8 := 93
@[inline] def lbrace : UInt8 := 123
@[inline] def rbrace : UInt8 := 125

end Grip.Ascii

/-! ### Sanity guards. -/
section
open Grip.Ascii

#guard (isWs 32 && isWs 10 && isWs 9 && isWs 13) == true
#guard isWs 65 == false
#guard (isDigit 47 == false) && (isDigit 48 == true) && (isDigit 57 == true) && (isDigit 58 == false)
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
```

- [ ] **Step 2: Add `Grip.Ascii` to the umbrella and re-export `Grip.Char`**

Modify `Grip.lean` -- replace `import Grip.Parser` block so the umbrella re-exports the Char and Ascii layers too:

```lean
import Grip.Parser
import Grip.Char
import Grip.Ascii
```

- [ ] **Step 3: Build to verify the guards pass**

Run: `lake build Grip.Ascii`
Expected: `Build completed successfully`. (Any false `#guard` aborts the build.)

- [ ] **Step 4: Commit**

```bash
git add Grip/Ascii.lean Grip.lean
git commit -m "feat: Grip.Ascii -- named byte predicates, constants, and code"
```

---

## Task 2: `Grip.Combinators` byte parsers

**Files:**
- Create: `Grip/Combinators.lean`
- Modify: `Grip.lean`

**Interfaces:**
- Consumes: `Grip.Ascii.*` (Task 1); core `GParser.{byte, satisfy, takeWhile, takeWhile1}` from `Grip.Graded`.
- Produces: `Grip.GParser.{byteC : Char → GParser conditional Unit, ws : GParser flexible Nat, ws1 : GParser conditional Nat, digit hexDigit letter alphaNum upper lower : GParser conditional UInt8, oneOf noneOf : List UInt8 → GParser conditional UInt8}`.

- [ ] **Step 1: Create `Grip/Combinators.lean` with the byte parsers**

```lean
/-
Copyright 2026 Jonathan Cubides. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grip.Parser
import Grip.Ascii

/-!
# Grip.Combinators -- a megaparsec-style vocabulary over the grip core

Ready-made byte parsers (`ws`, `digit`, `oneOf`, ...) and higher-order combinators
(`sepBy`, `between`, `choice`, ...), each with a precise grade where the grade is stable,
or at the `Parser` (fallible) face where it depends on runtime data. Batteries-only.
-/

namespace Grip

open Grip.Ascii

/-- Match the byte of an ASCII `Char` literal: `byteC '{'` matches `{`. -/
@[inline] def GParser.byteC (c : Char) : GParser conditional Unit := GParser.byte (Ascii.code c)

/-- Skip zero or more whitespace bytes; returns the count. -/
@[inline] def GParser.ws : GParser flexible Nat := GParser.takeWhile Ascii.isWs
/-- Skip one or more whitespace bytes; returns the count. -/
@[inline] def GParser.ws1 : GParser conditional Nat := GParser.takeWhile1 Ascii.isWs
/-- One decimal digit byte. -/
@[inline] def GParser.digit : GParser conditional UInt8 := GParser.satisfy Ascii.isDigit
/-- One hex digit byte. -/
@[inline] def GParser.hexDigit : GParser conditional UInt8 := GParser.satisfy Ascii.isHexDigit
/-- One ASCII letter byte. -/
@[inline] def GParser.letter : GParser conditional UInt8 := GParser.satisfy Ascii.isAlpha
/-- One letter-or-digit byte. -/
@[inline] def GParser.alphaNum : GParser conditional UInt8 := GParser.satisfy Ascii.isAlphaNum
/-- One uppercase letter byte. -/
@[inline] def GParser.upper : GParser conditional UInt8 := GParser.satisfy Ascii.isUpper
/-- One lowercase letter byte. -/
@[inline] def GParser.lower : GParser conditional UInt8 := GParser.satisfy Ascii.isLower
/-- One byte from `bs`. -/
@[inline] def GParser.oneOf (bs : List UInt8) : GParser conditional UInt8 :=
  GParser.satisfy (fun b => bs.contains b)
/-- One byte not in `bs`. -/
@[inline] def GParser.noneOf (bs : List UInt8) : GParser conditional UInt8 :=
  GParser.satisfy (fun b => !bs.contains b)

end Grip

/-! ### Sanity guards (byte parsers). -/
section
open Grip

#guard (GParser.run? GParser.digit "7".toUTF8) == some 55
#guard (GParser.run? GParser.digit "x".toUTF8) == none
#guard (GParser.run? GParser.hexDigit "f".toUTF8) == some 102
#guard (GParser.run? (GParser.byteC '{') "{".toUTF8) == some ()
#guard (GParser.run? GParser.ws "  \t x".toUTF8) == some 3
#guard (GParser.run? GParser.ws1 "x".toUTF8) == none
#guard (GParser.run? (GParser.oneOf [97, 98]) "b".toUTF8) == some 98
#guard (GParser.run? (GParser.noneOf [97, 98]) "b".toUTF8) == none

end
```

- [ ] **Step 2: Add `Grip.Combinators` to the umbrella**

Modify `Grip.lean` -- add the import:

```lean
import Grip.Combinators
```

- [ ] **Step 3: Build to verify**

Run: `lake build Grip.Combinators`
Expected: `Build completed successfully`.

- [ ] **Step 4: Commit**

```bash
git add Grip/Combinators.lean Grip.lean
git commit -m "feat: Grip.Combinators byte parsers (ws, digit, oneOf, byteC, ...)"
```

---

## Task 3: `Grip.Combinators` higher-order combinators

**Files:**
- Modify: `Grip/Combinators.lean`

**Interfaces:**
- Consumes: core `GParser.{map, map2, seqR, seqL, alt, many, foldMany, pure, fix}`, `Parser`, `GParser.weakenFallible`, `Monad`/`Alternative` `Parser` instances.
- Produces: `Grip.GParser.{between, sepBy1, sepBy, endBy, skipMany, skipMany1, option, optional, notFollowedBy, manyTill, chooseG}` and `Grip.choice`, `Grip.count`.

- [ ] **Step 1: Add the higher-order combinators inside `namespace Grip` (before the guards section)**

```lean
variable {α β γ : Type} {g g₁ g₂ : Grade} {ge : Necessity}

/-- `p` between `open`/`close`; grades multiply (megaparsec order: open, close, body). -/
@[inline] def GParser.between (open_ : GParser g₁ β) (close : GParser g₂ γ) (p : GParser g α) :
    GParser (g₁ * g * g₂) α :=
  GParser.seqR open_ (GParser.seqL p close)

/-- One or more `p` separated by `sep`. Both must always consume. -/
@[inline] def GParser.sepBy1 (p : GParser conditional α) (sep : GParser conditional β) :
    GParser conditional (List α) :=
  GParser.map2 (fun x xs => x :: xs) p (GParser.many (GParser.seqR sep p))

/-- Zero or more `p` separated by `sep`. -/
@[inline] def GParser.sepBy (p : GParser conditional α) (sep : GParser conditional β) :
    GParser flexible (List α) :=
  GParser.alt (GParser.sepBy1 p sep) (GParser.pure [])

/-- Zero or more `p` each followed by `sep`. -/
@[inline] def GParser.endBy (p : GParser conditional α) (sep : GParser conditional β) :
    GParser flexible (List α) :=
  GParser.many (GParser.seqL p sep)

/-- Skip zero or more `p` (always-consuming); returns the count skipped. -/
@[inline] def GParser.skipMany (p : GParser ⟨ge, always⟩ α) : GParser flexible Nat :=
  GParser.foldMany (fun n _ => n + 1) 0 p

/-- Skip one or more `p`; returns the count. -/
@[inline] def GParser.skipMany1 (p : GParser ⟨ge, always⟩ α) : GParser conditional Nat :=
  GParser.map2 (fun _ n => n + 1) p (GParser.skipMany p)

/-- `p`, or `x` if `p` fails without a real match. -/
@[inline] def GParser.option (x : α) (p : GParser g α) := GParser.alt p (GParser.pure x)

/-- `some` of `p`, or `none`. -/
@[inline] def GParser.optional (p : GParser g α) :=
  GParser.alt (GParser.map some p) (GParser.pure none)

/-- Succeed (consuming nothing) exactly when `p` fails. -/
@[inline] def GParser.notFollowedBy (p : GParser g α) : GParser ⟨possibly, never⟩ Unit where
  run := fun arr q => match p.run arr q with | .ok _ _ => .error ⟨q, []⟩ | .error _ => .ok () q
  cwit := by
    intro arr q a q' h
    split at h
    · exact absurd h (by simp)
    · simp only [ParseResult.ok.injEq] at h; omega
  ewit := by intro he; exact absurd he (by decide)
  swit := by intro he; exact absurd he (by decide)

/-- Zero or more `p` (always-consuming) until `endp` matches; `endp` is discarded. -/
@[inline] def GParser.manyTill (p : GParser ⟨ge, always⟩ α) (endp : GParser conditional β) :
    GParser conditional (List α) :=
  GParser.fix fun rec =>
    GParser.alt (GParser.map (fun _ => ([] : List α)) endp) (GParser.map2 (fun x xs => x :: xs) p rec)

/-- Ordered choice over a non-empty list at a single grade `g`
(`Grade.choice g g = g` definitionally). -/
@[inline] def GParser.chooseG (x : GParser g α) (xs : List (GParser g α)) : GParser g α :=
  xs.foldl GParser.alt x

/-- Ordered choice at the ungraded `Parser` face; empty list fails. -/
@[inline] def choice (ps : List (Parser α)) : Parser α :=
  ps.foldr GParser.alt (GParser.weakenFallible GParser.fail)

/-- Exactly `n` copies of `p`, at the `Parser` face (grade is `n`-dependent). -/
def count (n : Nat) (p : Parser α) : Parser (List α) := do
  match n with
  | 0 => return []
  | n + 1 => let x ← p; let xs ← count n p; return (x :: xs)
```

- [ ] **Step 2: Add guards for the higher-order combinators (extend the guards section)**

```lean
-- higher-order
#guard (GParser.run? (GParser.sepBy GParser.digit (GParser.byteC ',')) "1,2,3".toUTF8)
        == some [49, 50, 51]
#guard (GParser.run? (GParser.sepBy GParser.digit (GParser.byteC ',')) "".toUTF8) == some []
#guard (GParser.run? (GParser.between (GParser.byteC '(') (GParser.byteC ')') GParser.digit) "(5)".toUTF8)
        == some 53
#guard (GParser.run? (GParser.endBy GParser.digit (GParser.byteC ';')) "1;2;".toUTF8) == some [49, 50]
#guard (GParser.run? (GParser.skipMany GParser.digit) "123x".toUTF8) == some 3
#guard (GParser.run? (GParser.option (65 : UInt8) GParser.digit) "x".toUTF8) == some 65
#guard (GParser.run? (GParser.optional GParser.digit) "x".toUTF8) == some none
#guard (GParser.run? (GParser.notFollowedBy GParser.digit) "x".toUTF8) == some ()
#guard (GParser.run? (GParser.notFollowedBy GParser.digit) "5".toUTF8) == none
#guard (GParser.run? (GParser.manyTill GParser.letter (GParser.byteC '.')) "abc.".toUTF8)
        == some [97, 98, 99]
#guard (GParser.run? (GParser.chooseG (GParser.byteC 'a') [GParser.byteC 'b']) "b".toUTF8) == some ()
#guard (GParser.run? (choice [GParser.weakenFallible (GParser.byteC 'a'),
                              GParser.weakenFallible (GParser.byteC 'b')]) "b".toUTF8) == some ()
#guard (GParser.run? (count 3 (GParser.weakenFallible GParser.digit)) "123".toUTF8)
        == some [49, 50, 51]
```

- [ ] **Step 3: Build to verify all guards pass**

Run: `lake build Grip.Combinators`
Expected: `Build completed successfully`.

If `chooseG` fails to type-check on `Grade.choice g g = g` not reducing, change its
signature to the `Parser` face (`chooseG (x : Parser α) (xs : List (Parser α)) : Parser α`)
and note the fallback in the module doc. This is the one anticipated failure point.

- [ ] **Step 4: Commit**

```bash
git add Grip/Combinators.lean
git commit -m "feat: Grip.Combinators higher-order (sepBy, between, choice, manyTill, ...)"
```

---

## Task 4: Refactor Sexp and Lambda

**Files:**
- Modify: `examples/Sexp.lean`, `examples/Lambda.lean`

**Interfaces:**
- Consumes: `Grip.Ascii.*`, `Grip.GParser.{byteC, sepBy, ws, ...}` (Tasks 1-3).

- [ ] **Step 1: Sexp -- import and replace predicates/bytes**

In `examples/Sexp.lean`: change `import Grip.Parser` to `import Grip` (umbrella now carries Ascii/Combinators). Delete the local `isWs`; replace uses with `Ascii.isWs`. Replace `isAtomByte` body's magic numbers with `Ascii` where clearer (keep it a local def -- it is grammar-specific). Replace `GParser.byte 40`/`41` with `GParser.byteC '('`/`')'`. Keep `ws := GParser.takeWhile Ascii.isWs` or use `GParser.ws`.

- [ ] **Step 2: Build Sexp**

Run: `lake build Sexp`
Expected: `Build completed successfully` (its existing `#guard`s still hold).

- [ ] **Step 3: Lambda -- same treatment**

In `examples/Lambda.lean`: `import Grip`; drop local `isWs`/`isAlpha` for `Ascii.isWs`/`Ascii.isAlpha`; `GParser.byte 40/41/92/46` → `GParser.byteC '('/')'/'\\'/'.'`; use `GParser.ws` for whitespace skipping.

- [ ] **Step 4: Build Lambda**

Run: `lake build Lambda`
Expected: `Build completed successfully`.

- [ ] **Step 5: Commit**

```bash
git add examples/Sexp.lean examples/Lambda.lean
git commit -m "refactor(examples): Sexp and Lambda use Grip.Ascii/Combinators"
```

---

## Task 5: Refactor Http, Toml, Yaml

**Files:**
- Modify: `examples/Http.lean`, `examples/Toml.lean`, `examples/Yaml.lean`

**Interfaces:**
- Consumes: `Grip.Ascii.*`, `Grip.GParser.{byteC, sepBy, sepBy1, choice, chooseG, option, ...}`.

- [ ] **Step 1: Http** -- `import Grip`; `isUpper`→`Ascii.isUpper`; `isVersionByte`/`isNameByte` keep local (grammar-specific) but use `Ascii` constants inside; `GParser.byte 32/58/13/10` → `GParser.byteC ' '/':'/'... '` or `Ascii.space`/`Ascii.colon`; `GParser.string "HTTP/"` stays. Build: `lake build Http`.

- [ ] **Step 2: Toml** -- `import Grip`; `isAlpha`/`isKeyByte`/`isIntByte` use `Ascii` predicates/constants; `GParser.byte 61/34` → `GParser.byteC '='/'\"'`. Consider `chooseG`/`dispatch` for the value branch (keep `dispatch`). Build: `lake build Toml`.

- [ ] **Step 3: Yaml** -- `import Grip`; `isWs`/`isPlainByte` use `Ascii`; array/object bodies may use `sepBy` where it reads clearly, else keep as-is; `GParser.byte 91/93/123/125/44/58/34` → `GParser.byteC '['/']'/'{'/'}'/','/':'/'\"'`. Build: `lake build Yaml`.

- [ ] **Step 4: Build all three, confirm guards**

Run: `lake build Http Toml Yaml`
Expected: `Build completed successfully`.

- [ ] **Step 5: Commit**

```bash
git add examples/Http.lean examples/Toml.lean examples/Yaml.lean
git commit -m "refactor(examples): Http, Toml, Yaml use Grip.Ascii/Combinators"
```

---

## Task 6: Refactor Json (measured)

**Files:**
- Modify: `examples/Json.lean`

**Interfaces:**
- Consumes: `Grip.Ascii.*`, `Grip.GParser.{byteC, sepBy, ...}`.

- [ ] **Step 1: Rename magic numbers to `Ascii` (no structural change)**

`import Grip`; `isWs`→`Ascii.isWs`; keep `isNumCh` local but use `Ascii.isDigit` inside; `GParser.byte 34/44/58/91/93/123/125` → `GParser.byteC '\"'/','/':'/'['/']'/'{'/'}'`. Keep `dispatch` + `foldMany` structure.

- [ ] **Step 2: Build and benchmark the renamed version**

Run: `lake build Json && lake exe bench`
Expected: `Build completed successfully`; `count=111130`; `parse_ms` ≈ 34 (rename must not change perf).

- [ ] **Step 3: Try the `sepBy` form of the array/object bodies**

Rewrite `arrayBody`/`objectBody` using `GParser.sepBy value (…comma…)` (values separated by `ws , ws`). Keep the top-level first-byte `dispatch`.

- [ ] **Step 4: Benchmark; keep only if within 15%**

Run: `lake exe bench`
Decision: if `parse_ms` ≤ ~39 (within 15% of ~34), keep the `sepBy` form. Otherwise `git checkout examples/Json.lean` to revert to the Step-1 renamed-but-dispatch version. Record the measured number.

- [ ] **Step 5: Commit**

```bash
git add examples/Json.lean
git commit -m "refactor(examples): Json uses Grip.Ascii (keeps dispatch fast path)"
```

---

## Task 7: Integration -- full build, bench, docs

**Files:**
- Modify: `bench/RESULTS.md` (only if Json perf changed), `docs/` note optional.

- [ ] **Step 1: Full build (core, tests, examples, bench)**

Run: `lake build Grip Test Examples bench`
Expected: `Build completed successfully`.

- [ ] **Step 2: grip-props unaffected (additive change) -- confirm**

Run: `cd grip-props && lake build`
Expected: `Build completed successfully` (the new modules add no obligations; grip-props imports `Grip` and is unaffected).

- [ ] **Step 3: Bench sanity**

Run: `lake exe bench`
Expected: `count=111130`; example lines present; `parse_ms` within the recorded range.

- [ ] **Step 4: Update RESULTS if Json perf moved; commit any doc change**

```bash
git add bench/RESULTS.md
git commit -m "docs: note Json perf after Ascii/Combinators refactor"
```

---

## Self-Review

**Spec coverage:** Ascii predicates/constants/helpers → Task 1. byte parsers → Task 2. higher-order (between/sepBy/sepBy1/endBy/skipMany/skipMany1/option/optional/count/choice/chooseG/notFollowedBy/manyTill) → Task 3. umbrella re-export of Char/Ascii/Combinators → Tasks 1-2. refactor 6 examples → Tasks 4-6. tests → `#guard`s in every task. JSON 15% rule → Task 6. All spec sections covered.

**Placeholders:** none -- every def and guard has concrete code. The one conditional ("revert if >15%") has an exact command and threshold.

**Type consistency:** predicate names `is*` match spec; `code`/`byteC`/`ws`/`sepBy`/`chooseG`/`choice`/`count` signatures match spec and are used consistently across tasks; `manyTill` takes `endp : conditional`; `notFollowedBy : ⟨possibly, never⟩ Unit`; all grade annotations match the core combinator grades.
