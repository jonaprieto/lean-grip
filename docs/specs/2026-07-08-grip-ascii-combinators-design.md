# grip Ascii + Combinators library -- design

## Goal

Factor the byte-literal magic numbers repeated across grip's six example parsers into a
named, predictable, batteries-only library, and add a megaparsec-style combinator
vocabulary on top of the existing core. Refactor the examples to use it.

## Motivation

Every example hardcodes the same bytes and predicates:

- whitespace `b == 32 || b == 10 || b == 9 || b == 13` (as `isWs`, six times)
- digits `48 ≤ b && b ≤ 57`, letters `(97≤b&&b≤122)||(65≤b&&b≤90)`
- delimiter bytes `34 " · 44 , · 58 : · 61 = · 91 [ · 93 ] · 123 { · 125 } · 92 \ · 46 . · 45 -`
- per-example predicates `isAtomByte`, `isPlainByte`, `isKeyByte`, `isNameByte`, `isIntByte`

Named, shared definitions remove the duplication and make parsers read declaratively.

## Non-goals

- Not a full `Data.Char` port. ASCII only (byte-level); the `Char` layer stays in `Grip.Char`.
- No new backtracking/`try` primitive beyond what `alt` already gives (grip's `alt` already
  retries the right branch from the original offset, i.e. full backtracking).
- Deliberately omitted from the megaparsec set (YAGNI, add later): `binDigitChar`,
  `charCategory`, `count'`, `someTill_`, `eitherP`, `lookAhead` (a value-returning peek).

## Architecture

Two new modules, both batteries-only, both re-exported by `Grip` (the umbrella must also
re-export `Grip.Char`, which it currently omits -- fix that here):

- **`Grip.Ascii`** -- pure byte layer. No parsers, no grades. Predicates (`UInt8 → Bool`),
  value helpers (`UInt8 → Nat`), named byte constants (`UInt8`), and `code : Char → UInt8`.
- **`Grip.Combinators`** -- the parser vocabulary. Ready-made byte parsers and higher-order
  combinators, each with a precise grade where the grade is stable, or at the `Parser`
  (fallible) face where it is not.

Dependency: `Grip.Combinators` imports `Grip.Ascii` and `Grip.Parser`.

## `Grip.Ascii`

All predicates `@[inline] def … : UInt8 → Bool`, `is`-prefixed:

| name | definition |
|------|------------|
| `isWs` | `b == 32 ‖ b == 10 ‖ b == 9 ‖ b == 13` (space, LF, tab, CR) |
| `isBlank` | `b == 32 ‖ b == 9` (space, tab) |
| `isDigit` | `48 ≤ b ∧ b ≤ 57` |
| `isHexDigit` | `isDigit b ‖ (97 ≤ b ∧ b ≤ 102) ‖ (65 ≤ b ∧ b ≤ 70)` |
| `isOctDigit` | `48 ≤ b ∧ b ≤ 55` |
| `isUpper` | `65 ≤ b ∧ b ≤ 90` |
| `isLower` | `97 ≤ b ∧ b ≤ 122` |
| `isAlpha` | `isUpper b ‖ isLower b` |
| `isAlphaNum` | `isAlpha b ‖ isDigit b` |
| `isControl` | `b ≤ 31 ‖ b == 127` |
| `isPrint` | `32 ≤ b ∧ b ≤ 126` |
| `isPunct` | `isPrint b ∧ ¬isAlphaNum b ∧ b ≠ 32` |

Value helpers:

- `digitValue : UInt8 → Nat := (·.toNat - 48)` (only meaningful when `isDigit`)
- `hexValue : UInt8 → Nat` (0-9 / a-f / A-F → 0..15; `0` otherwise)

Named byte constants (`UInt8`), one per common delimiter:
`space tab lf cr quote apostrophe backslash slash comma dot colon semicolon`
`dash plus equals star hash at lparen rparen lbracket rbracket lbrace rbrace`.

Char helper:

- `code : Char → UInt8 := fun c => UInt8.ofNat c.toNat` (low byte; ASCII-exact for `c < 128`).

`#guard` tests: each predicate at a boundary (e.g. `isDigit 47 = false`, `isDigit 48 = true`,
`isDigit 57 = true`, `isDigit 58 = false`); `code '{' = 123`; `hexValue 0x41 = 10`.

## `Grip.Combinators`

### Byte parsers

| name | grade | definition |
|------|-------|------------|
| `byteC c` | `conditional Unit` | `GParser.byte (Ascii.code c)` |
| `ws` | `flexible Nat` | `GParser.takeWhile Ascii.isWs` |
| `ws1` | `conditional Nat` | `GParser.takeWhile1 Ascii.isWs` |
| `digit` | `conditional UInt8` | `GParser.satisfy Ascii.isDigit` |
| `hexDigit` | `conditional UInt8` | `GParser.satisfy Ascii.isHexDigit` |
| `letter` | `conditional UInt8` | `GParser.satisfy Ascii.isAlpha` |
| `alphaNum` | `conditional UInt8` | `GParser.satisfy Ascii.isAlphaNum` |
| `upper` / `lower` | `conditional UInt8` | `GParser.satisfy Ascii.isUpper` / `isLower` |
| `oneOf bs` | `conditional UInt8` | `GParser.satisfy (bs.contains ·)` |
| `noneOf bs` | `conditional UInt8` | `GParser.satisfy (!bs.contains ·)` |

### Higher-order combinators

Grades chosen so the many-gate (`many`/`foldMany` need an always-consuming element) is
respected. `α β … : Type`, grade metavariables named `g …`.

- `between (open : GParser g₁ β) (close : GParser g₂ γ) (p : GParser g α) : GParser (g₁ * g * g₂) α`
  `:= GParser.seqR open (GParser.seqL p close)` (megaparsec argument order: open, close, body).
- `sepBy1 (p : GParser conditional α) (sep : GParser conditional β) : GParser conditional (List α)`
  `:= GParser.map2 (· :: ·) p (GParser.many (GParser.seqR sep p))`.
- `sepBy (p : GParser conditional α) (sep : GParser conditional β) : GParser flexible (List α)`
  `:= GParser.alt (sepBy1 p sep) (GParser.pure [])`.
- `endBy (p : GParser conditional α) (sep : GParser conditional β) : GParser flexible (List α)`
  `:= GParser.many (GParser.seqL p sep)`.
- `skipMany (p : GParser ⟨ge, always⟩ α) : GParser flexible Nat`
  `:= GParser.foldMany (fun n _ => n + 1) 0 p`.
- `skipMany1 (p : GParser ⟨ge, always⟩ α) : GParser conditional Nat`
  `:= GParser.map2 (fun _ n => n + 1) p (skipMany p)`.
- `option (x : α) (p : GParser g α) := GParser.alt p (GParser.pure x)` (grade = `Grade.choice g 1`, inferred).
- `optional (p : GParser g α) := GParser.alt (GParser.map some p) (GParser.pure none)` (grade inferred; result `Option α`).
- `count (n : Nat) (p : Parser α) : Parser (List α)` -- structural recursion on `n` in the
  `Parser` monad (`n = 0 → pure []`; `n+1 → do let x ← p; let xs ← count n p; pure (x :: xs)`).
  At the fallible face because the grade is `n`-dependent (n=0 never consumes/errs, n≥1 may).
- `choice (ps : List (Parser α)) : Parser α := ps.foldr GParser.alt failure` (empty → `failure`).
- `chooseG (x : GParser g α) (xs : List (GParser g α)) : GParser g α := xs.foldl GParser.alt x`
  -- non-empty, any single grade `g`; type-checks because `Grade.choice g g = g` definitionally
  (`min ge ge = ge`, `ge.ite gc gc = gc`).
- `notFollowedBy (p : GParser g α) : GParser ⟨possibly, never⟩ Unit` -- primitive `run`:
  `fun arr q => match p.run arr q with | .ok _ _ => .error ⟨q, []⟩ | .error _ => .ok () q`.
  Never consumes (`cwit`: success ⇒ `q = q'`); may fail (when `p` succeeds).
- `manyTill (p : GParser ⟨ge, always⟩ α) (endp : GParser ⟨possibly, always⟩ β) : GParser conditional (List α)`
  `:= GParser.fix fun rec => GParser.alt (GParser.map (fun _ => ([] : List α)) endp) (GParser.map2 (· :: ·) p rec)`.
  Each round consumes `p` or `endp`, so the always-consume clamp never fires on well-formed
  input; `endp` is discarded. (grip's `alt` backtracks the right branch from the original
  offset, so `endp` is effectively tried without commitment.)

### `#guard` tests

One acceptance guard per combinator against a tiny literal input, e.g.:
`GParser.run? (sepBy digit (byteC ',')) "1,2,3".toUTF8` (list length 3),
`between (byteC '(') (byteC ')') digit` on `"(5)"`,
`count 3 (… digit …)` etc., and negative cases (`notFollowedBy`, empty `sepBy`).

## Refactor of the examples

Replace inline magic numbers with `Ascii`/`Combinators` names in all six:

- **Json** -- swap literals for `Ascii.isWs`, `byteC`, `Ascii.isDigit`, etc. Keep the
  `dispatch` + `foldMany` hot path (it is the ~34ms benchmark). Try rewriting the
  array/object bodies with `sepBy`; **measure**, and keep the combinator form only if the
  parse stays within ~15% of ~34ms, otherwise keep `dispatch`/`foldMany` and only rename.
- **Sexp / Lambda / Http / Toml / Yaml** -- use `Ascii` predicates and, where they read
  more clearly, `sepBy` / `between` / `option` / `choice` / `chooseG`. Each example's
  existing `#guard`s stay as the integration test.

## Testing & CI

- Every `Ascii` predicate/constant and every `Combinators` entry gets a co-located `#guard`.
- The `core` CI job already builds `Grip Test Examples`; add the two modules to the `Grip`
  glob (already covered by `globs = ["Grip", "Grip.+"]`) and keep `Examples` building.
- Run `lake exe bench` after the Json refactor to confirm the ~34ms figure (or document the
  measured change).

## Risks

- **Json perf regression** from `sepBy`/`choice`. Mitigation: measure, keep `dispatch` if it
  regresses beyond ~15%.
- **`chooseG` grade defeq** (`Grade.choice g g = g`) must hold definitionally for `foldl` to
  type-check. If Lean does not reduce it transparently, fall back to `chooseG` at the
  `Parser` face (drop the precise-grade variant) -- a known escape hatch, not a blocker.
- **`manyTill`/`notFollowedBy`** are the only entries needing care; both rely on grip's
  backtracking `alt` and the `fix` clamp, which already exist.
