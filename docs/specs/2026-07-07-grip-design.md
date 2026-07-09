# grip design

> Point-in-time design spec (2026-07-07). Kept as a historical record; the numbers and
> version pins below reflect that date and are not maintained. Current benchmarks live in
> [`bench/RESULTS.md`](../../bench/RESULTS.md); the current API is the source.

Working name: `grip`. A fast, graded Lean 4 parser-combinator library that aims to
beat `fgdorais/lean4-parser` on speed and adoptability. Standalone private repo,
not part of prim-parser. The fast core is seeded by porting the technique in
prim-parser's `PrimParser/Byte.lean` (branch `graded-framework`).

Source of truth for the goal: https://gist.github.com/jonaprieto/d8f1d46362c916829e93603c7f0efc5a

## The bet

lean4-parser is a plain monad-transformer parser: stream-generic, batteries-only,
`partial def` recursion, good Char/Unicode/RegEx, but no static guarantees and not
proven total. grip keeps that ergonomics and dependency profile while adding two
things:

1. A byte-level fast path that ties or beats attoparsec.
2. Grades as an opt-in static safety layer. Grades are a feature, not a tax.

## Name

`grip` is free of clashes with parser-combinator libraries in Haskell (Hackage),
OCaml (opam), Agda, and Coq/Rocq (checked against parseque, agdarsec, parsec,
megaparsec, attoparsec, angstrom). It is also absent from Hackage, opam, and the
Lean reservoir. The Python "grip" readme previewer is a different domain and
language, so it does not clash.

## Two packages

The core stays mathlib-free so downstream libraries never transitively acquire
mathlib. This uses prim-parser's own proven sub-package pattern: its `docbuild/`
package requires the parent via `path = "../"`.

1. `grip` (core). The parser, grades, erased soundness witnesses, and a small
   hand-rolled `Necessity`/`Grade` algebra. Dependency: batteries only. This is
   what downstream libraries depend on.
2. `grip-props` (properties, opt-in). The machine-checked metatheory:
   `LawfulGradedMonad` law instances, grade-soundness meta-theorems, the
   totality-not-productivity and choice-grade-impossibility results. Dependencies:
   grip plus mathlib. Nobody pulls this unless they want the proofs.

Separate lakefiles. `lean-toolchain` pinned to `leanprover/lean4:v4.28.0` in both.

## Folder structure

One private repo `github.com/jonaprieto/grip` at `~/research/grip`. Core package at
the repo root, `grip-props` as a sub-package directory.

```
grip/                     repo root = core package "grip"  (deps: batteries only)
  lean-toolchain          leanprover/lean4:v4.28.0
  lakefile.toml
  Grip.lean               public root, re-exports the modules below
  Grip/
    Necessity.lean        3-valued never/possibly/always + sup/inf/ite/le + lemmas
    Grade.lean            Grade = errors x consumes; mul(=max)/one/choice; named grades; consumptionWitness
    Error.lean            ParseError: byte offset -> line/col, source line + caret, label / <?>, expected-set merge
    Graded.lean           GParser g a: run (ByteArray -> Nat -> Option (a x Nat)) + erased cwit/ewit/swit; weaken; graded combinators; many-gate
    Parser.lean           Parser := GParser fallible; Monad/Alternative/MonadExcept instances at the idempotent fallible grade
    Byte.lean             byte primitives ported from prim-parser (satisfy/byte/seq/alt/takeWhile/foldFwd/nat/many)
    Char.lean             UTF-8/Char decoding layer above the byte core
  examples/Json.lean      JSON parser wired to canada.json
  test/                   #guard smoke tests + unit tests
  bench/
    Bench.lean            lake exe bench: best-of-N, prints count=... parse_ms=...
    JCombo.lean           packed-UInt64 JSON specialization (needed to clear attoparsec)
    data/canada.json      vendored ~2.1MB fixture
    hyperfine.sh, RESULTS.md, results.svg, mkchart.sh
  .github/workflows/ci.yml
  README.md
  grip-props/             sub-package, own lakefile  (deps: grip + mathlib)
    lean-toolchain, lakefile.toml
    GripProps.lean
    GripProps/
      Lawful.lean         LawfulGradedMonad/Functor/Applicative instances
      GradeSound.lean     grade-soundness meta-theorems
      Productivity.lean   totality != productivity (fix limitation), ported
      ChoiceGrade.lean    choice-grade impossibility result
```

No god modules. Each file is one concern. None should grow past a few hundred lines.

## Grade algebra, batteries-only

prim-parser's `Grade` uses mathlib's `Monoid` and `Necessity` uses mathlib's `⊔`/`⊓`
lattice. grip core hand-rolls all of it:

- `Necessity` is a 3-constructor inductive `never | possibly | always`.
- `sup`, `inf`, `ite`, and `le` are plain `def`s. The handful of lemmas the witness
  proofs need (`max_always`, `max_never`, `min_always`, `min_never`, `sup_comm`, and
  friends) are proved by `cases`/`decide` on the finite type. No mathlib.
- `Grade` is `{ errors : Necessity, consumes : Necessity }` with `mul` (= componentwise
  max), `one` (= `⟨never, never⟩`, pure), and `choice`. Named grades: `conditional`,
  `flexible`, `fallible`, `pure`, `lookahead`, `empty`, `impossible`.
- `consumptionWitness n m : Necessity → Prop` (`always ⇒ n<m`, `possibly ⇒ n≤m`,
  `never ⇒ n=m`) plus its `trans`, `ite_left`, `ite_right`, `rfl` helpers.

The mathlib-facing `Monoid Grade`, `Max`, lattice instances, and the graded-monad law
instances move to `grip-props`.

## One graded type, with an ungraded face

There is a single parser type. Grades are opt-in by writing a precise index instead of
the ungraded alias.

- `GParser g α` is the type: a `run : ByteArray → Nat → Option (α × Nat)` plus three
  erased `Prop` soundness witnesses `cwit`/`ewit`/`swit`, exactly the trio from
  `Byte.lean`:
  - `cwit`: a successful parse advances the offset exactly as `g.consumes` claims.
  - `ewit`: a grade claiming `always`-error never succeeds.
  - `swit`: a grade claiming `never`-error always succeeds.
  Witnesses are proof-irrelevant and erase, so the parser runs at the bare `Option`
  fast path with no runtime cost.

- `abbrev Parser α := GParser fallible α` is the drop-in face for lean4-parser porters.

Why one type rather than a separate ungraded base plus a graded wrapper. Lean's `Monad`
class fixes the type constructor, but graded bind changes the index
(`GParser g α → (α → GParser g' β) → GParser (g*g') β`), so a grade-indexed type cannot
be a plain `Monad`. The fix is to instance the standard classes at a grade that is a
fixed point. `fallible = ⟨possibly, possibly⟩` is idempotent under both `mul` and
`choice` (`fallible * fallible = fallible`, `choice fallible fallible = fallible`), and
at `fallible` all three witnesses are vacuous (`cwit` only asks forward progress,
`ewit` needs `errors = always`, `swit` needs `errors = never`, both false). So
`GParser fallible` carries genuine `Monad`, `Alternative`, and `MonadExcept` instances
(`bind` and `<|>` stay at `fallible`; `failure` is the vacuous-witness `fun _ _ => none`).
A lean4-parser user writes at `Parser` and never sees a grade. No second structure, no
duplication, no runtime wrapper.

A `weaken` coercion moves a precise parser into a less precise grade: `always` and
`never` consumption both imply the `possibly` version, and any `errors` value implies
`possibly`, so every grade weakens to `fallible`. This is registered as a `Coe` where
it helps, so precise combinators drop into `Parser` do-blocks. Weakening only ever
loosens, never strengthens.

The one grade payoff to preserve and market: `many`, `foldMany`, and `some` demand an
always-consuming parser at the type level (`GParser ⟨_, always⟩`). `pure x` has grade
`⟨never, never⟩`, and `never` cannot strengthen to `always`, so `many (pure x)`, the
classic parsec/attoparsec infinite-loop footgun, is a compile error. This is the
headline feature.

## Usage: two tiers, one library

The library primitives carry precise grades (`letter : GParser conditional Char`,
`byte : GParser conditional Unit`, and so on). A user chooses how much to care; the
functions and the runtime are the same either way.

- Drop-in tier. Write at `Parser`, no grades, plain `do`, exactly like lean4-parser.
  Precise library primitives compose transparently and weaken into the block. The
  `many` gate still fires, because it is carried by the primitives' types, not by the
  user's annotations. So `many (pure ())` is a compile error even in ungraded code.
- Careful tier. State a precise grade to enforce and export a guarantee across your own
  combinator (`def number : GParser conditional Nat := gdo ...`). If the body does not
  actually honor the claim, the annotation fails to elaborate (`cwit` cannot prove
  `q < q'`). Downstream users of `number` inherit a safe `many number`.

The knob is annotation, not a different type. No annotation lets Lean infer the precise
grade from the combinators used. `: GParser conditional α` documents and enforces a
contract. `: Parser α` opts out into the ungraded face.

Two do-notations carry the mixing:

- plain `do` runs at `fallible` (the `Monad (GParser fallible)` instance). It mixes any
  graded actions, each weakened in, and produces an ungraded result.
- `gdo` (graded do, as in prim-parser) uses graded-bind and keeps the precise product
  grade. This is how a precise combinator is built.

Mixing directions:

- Precise to `Parser` (down) is free: every grade weakens to `fallible` via `weaken`,
  registered as a `Coe` where it helps.
- `Parser` to precise (up) is not free: a value already typed `Parser` has erased its
  proof, so a precise grade comes from building with precise primitives under `gdo`, not
  from relabeling a fallible value.
- Escape hatch: construct a `GParser g` directly by giving `run` and discharging the
  `cwit`/`ewit`/`swit` obligations by hand. Available, but you prove what you claim.

```lean
open Grip

-- most of the grammar: ungraded, plain `do`
def spaces : Parser Unit := ...
def token (p : Parser α) : Parser α := do let x ← p; spaces; pure x

-- one custom piece you want precise (to feed `many`): built with `gdo`
def digits1 : GParser conditional Nat := gdo        -- provably always-consuming
  let d ← digit
  foldMany (fun n c => n * 10 + c) d.toNat digit

-- use the same combinator both ways
def intLit  : Parser Nat                  := token digits1   -- down: free (weaken)
def intList : GParser flexible (List Nat) := many digits1    -- up-use: allowed, digits1 always-consumes
```

Grade-specialization (a precise `GParser` index for safety) is orthogonal to runtime
performance specialization (`@[specialize]`, the packed-UInt64 JSON path). Different
meanings of "specialize."

## Scope: byte-first, Char layer on top

- Fast core over `ByteArray` plus `Nat` offsets, results `Option (α × Nat)`, all
  combinators `@[inline]`/`@[specialize]` so Lean fuses them into the grammar. Port
  `satisfy`/`byte`/`seq`/`alt`/`takeWhile`/`foldFwd`/`nat`/`many` from `Byte.lean` and
  keep the runtime bounds-guard totality of `foldFwd`/`scanFwd`/`natFwd`.
- A UTF-8/Char decoding layer above the byte core for Char consumers. The fast path
  stays byte-level.
- A JCombo-style packed-UInt64 specialization is allowed for the JSON benchmark to
  clear attoparsec (the polymorphic `Option (α × Nat)` form ties attoparsec at ~19 ms;
  the packed form hit 18.3 ms in prim-parser).

## Errors

The hot loop stays `Option (α × Nat)` for speed. User-facing entry points track the
furthest-failure offset and reconstruct a `ParseError` on failure: byte offset to
line/col, source line plus caret, megaparsec-style `<?>`/`label`, and expected-set
merge on `<|>`. Ported from prim-parser's `ParseError`. Failure in the public API
carries position, never a bare `none`.

## Benchmark

The benchmark exists before the first real combinator. Milestone 0 ships a runnable
`lake exe bench` that parses canada.json and prints `parse_ms`, even against a stub.
Every combinator added afterward is measured against it. A change that regresses
`parse_ms` is treated as a failure.

- `lake exe bench` under `bench/`, self-timed best-of-N inner loop, printing
  `count=... parse_ms=...`.
- Fixture vendored at `bench/data/canada.json` (the standard nativejson-benchmark file,
  ~2.1 MB, copied from prim-parser's `bench-data/canada.json`). Deterministic input, no
  network at run time.
- `bench/hyperfine.sh` wraps the exe for wall-clock comparison against attoparsec and
  lean4-parser.
- `bench/RESULTS.md` tracks input, ms, and vs-attoparsec, updated as the core matures.

## README benchmarks and chart

`bench/mkchart.sh` turns `RESULTS.md` into a committed `bench/results.svg` bar chart
(grip vs attoparsec vs lean4-parser, `parse_ms`), hand-written SVG with no chart
library. The README embeds the SVG and a shields.io endpoint badge for the latest
`parse_ms`. The main README is updated with the benchmark table and chart as the core
matures.

## CI, branch protection, badges

`.github/workflows/ci.yml`, three jobs on `leanprover/lean-action@v1` (installs elan
from `lean-toolchain`, runs `lake build` plus `lake test`):

- `core`: build and test the `grip` core package. Batteries-only, so fast. Runs the
  `#guard` smoke tests and the JSON example.
- `bench`: build `lake exe bench`, run it on `bench/data/canada.json`, echo `parse_ms`
  into the job summary. Smoke on PRs (assert it parses, count correct), full timing on
  push to main.
- `props`: build and test `grip-props`. Run `lake exe cache get` before `lake build`
  to fetch the mathlib olean cache. Heavy, kept separate so core CI stays fast.

Branch protection on `main` via `gh api`: require pull requests, require the `core`,
`bench`, and `props` checks green, no direct pushes. README badges: CI status, latest
bench `parse_ms`, license (Apache-2.0), and Lean toolchain version.

## Style

Apache-2.0 header. A `/-- ... -/` doc-comment on every combinator stating accept, fail,
and consume behavior. `@[inline]`/`@[specialize]` on hot paths. `test/` and `examples/`
with a JSON parser at minimum, wired to the canada.json benchmark. Matches the fgdorais
house style so downstream feels at home.

## Perf bar (acceptance)

Parse canada.json. Target: the byte core ties or beats attoparsec (~19.5 ms) and beats
lean4-parser. Report `parse_ms` in the hyperfine harness. Speed is a gate, not a
nice-to-have.

## Documentation (Verso, deferred)

The gist did not request Verso; the user did. Verso is Lean's doc-authoring system and
would be a third Lake package with its own toolchain-version constraint. It is deferred
to Milestone 3 so it never blocks the CI-green-from-commit-1 guarantee. Before wiring
it, confirm a Verso tag compatible with Lean v4.28.0. M0 through M2 ship a plain README
plus Apache-header doc-comments on every combinator, as the gist requires.

## Non-goals (do not build)

- No stream-genericity beyond bytes plus a Char layer. Concrete `ByteArray` is the
  speed.
- No RegEx engine, no BNF DSL. That is v2 material.
- No left-recursion or productivity solver. Document the `fix` limitation honestly (see
  prim-parser's `Productivity.lean`, ported to `grip-props`) instead of solving it.
- No mathlib in core, ever.

## Milestones

Full plan up front, each milestone kept minimal, focused signed commits.

- M0 skeleton. Two packages wired, toolchain pinned, canada.json vendored, stub
  `lake exe bench` prints parse_ms, CI 3 jobs green on the first commit, branch
  protection set, README with badges. All green before any combinator.
- M1 core. Base `Parser` plus instances, byte primitives ported, the always-consume
  `many` gate, `ParseError`, one JSON example parsing canada.json with a printed
  `parse_ms` that clears the bar, README benchmarks plus chart. Prove nothing yet.
- M2 props. `grip-props` with `LawfulGradedMonad` instances, grade-soundness
  meta-theorems, totality-not-productivity, choice-grade impossibility.
- M3 docs. Verso, once a v4.28.0-compatible tag is confirmed.

## Commit and CI discipline

Every commit on every branch is independently CI-green. History is built
commit-by-commit, verifying CI at each step, with fixes amended into the commit that
introduced the problem (no separate "fix CI" commits). All commits GPG/SSH signed and
Verified. `main` is altered only by merging a PR whose checks are green.
