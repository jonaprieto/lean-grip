# JSON conformance: RFC-8259 parser + JSONTestSuite harness

Date: 2026-07-13
Status: approved, pending implementation plan

## Problem

grip's `examples/Json.lean` is not an RFC-8259 parser. It is a deliberately loose
*leaf-counter* built for the benchmark:

- `number = takeWhile1 isNumCh` accepts `1.2.3`, `1e`, `--`, `00`.
- `keyword = takeWhile1 isAlpha` accepts `truue`, `nulll`, any letter run.
- `jstring` accepts any bytes between quotes: no `\uXXXX` / escape / control-char validation.
- `json` does not require EOF, so trailing garbage passes.

`nst/JSONTestSuite` is a *conformance* suite, not a benchmark: accept every `y_*` file,
reject every `n_*` file, `i_*` is implementation-defined. Run against today's parser it
would produce a wall of `n_*` failures, because the parser was never built to reject.

"Follow JSONTestSuite" therefore means: build a real strict parser, gate it on the corpus,
and make grip a first-class JSONTestSuite `parsers/` entry runnable by the official driver.
Then benchmark the *strict* parser honestly.

## Goals

1. `examples/Json.lean` becomes a **grammar-strict** RFC-8259 validator (defined below),
   still returning a leaf **count** (`Nat`) so the benchmark's `count=111130` cross-check
   and the accept/reject signal both come from one parse.
2. A self-contained, offline **CI gate** over a vendored copy of the JSONTestSuite corpus.
3. grip exposed as a JSONTestSuite `parsers/` entry: a wrapper honoring the exit-code
   protocol, plus opt-in infra to run the *official* `run_tests.py` restricted to grip.
4. Benchmark revamped for honesty: strict-match the in-repo Lean baselines to the same
   grammar; disclose the loose cross-language baselines; rewrite `RESULTS.md`.

## Non-goals (the grammar-strict ceiling)

Documented limitations, each with an upgrade path noted in code and RESULTS:

- **No UTF-8 byte validation.** Bytes `>= 0x80` inside strings pass opaque. A small set of
  invalid-UTF-8 `n_*` files are consequently accepted; they are an explicit, commented
  allow-list, not silent passes. Upgrade path: add a UTF-8 validating scan on the string body.
- **No deep-nesting stack safety.** `GParser.fix` recurses on the Lean call stack, bounded
  by bytes remaining. Pathologically deep inputs (`n_structure_100000_opening_arrays`) can
  overflow the process, so those files are an explicit excluded list in the runner. Upgrade
  path: a nesting-depth limit or trampolined `fix`.
- **No DOM / value tree.** Validate-and-count only. Upgrade path: a value-building variant.

## Parser design (`examples/Json.lean`)

Built entirely from existing grip combinators; grip's core library is not modified. Only
`eof` is composed locally. Relevant API (verified): `GParser.string` (exact literal),
`optional`, `satisfy`, `byteC`, `dispatch`, `takeWhile`, `takeWhile1`, `foldMany`, `fix`,
`seqR`/`seqL`/`map2`, `Ascii.isDigit`/`isHexDigit`, `weakenFallible`. There is no `peek`,
no `eof`, and `run?`/`parse` do **not** enforce full consumption.

### EOF

```
-- succeeds (no consumption) exactly when no byte remains
def eof := GParser.notFollowedBy (GParser.satisfy (fun _ => true))
```

`satisfy` fails only when there is no byte to consume, so `notFollowedBy` of it succeeds
exactly at end of input.

### Top level

```
json := ws *> value <* ws <* eof   -- weakenFallible to the Parser face
```

EOF is what turns trailing garbage, `01`, `[1,]`, and `1 2` into rejects.

### number (RFC 8259)

```
number = '-'?  ( '0' | [1-9][0-9]* )  ( '.' [0-9]+ )?  ( [eE] [+-]? [0-9]+ )?
```

Composition sketch: `optional (byteC '-')` then `alt (byteC '0') (satisfy isDigit19 *> takeWhile isDigit)`
then `optional ('.' *> takeWhile1 isDigit)` then `optional ([eE] *> optional [+-] *> takeWhile1 isDigit)`.
`isDigit19 = fun b => '1' <= b && b <= '9'`. Leading-zero (`01`) and `1 2` are rejected by
the EOF / structural check, not by number itself.

**Implementation risk to resolve during TDD:** grip's `alt` is megaparsec-style
furthest-failure merge, and `conditional` parsers consume on the matched prefix before a
later sub-parser fails (e.g. `.` consumed, then `[0-9]+` missing). The exact backtracking
behavior of `optional`/`alt` on a partially-consumed failing branch must be pinned down
against the corpus; the number and string parsers are where this bites. JSONTestSuite is the
oracle: build test-first, let `n_number_*` / `n_string_*` files drive the fixes.

### keyword

```
keyword = string "true" | string "false" | string "null"
```

Exact match via `GParser.string`; rejects `truue`, `nul`, `True`.

### string (validating)

```
string = '"' ( unescaped | escape )* '"'
unescaped = byte b with  b >= 0x20  and  b != '"'  and  b != '\'
escape    = '\' ( one of  " \ / b f n r t  |  'u' hex hex hex hex )
hex       = Ascii.isHexDigit
```

Rejects control chars (`< 0x20`) unescaped, unknown escapes (`\x`), and short `\u`.
Correctness-first: body as `foldMany` over `escape <|> unescaped`. Bytes `>= 0x80` pass
opaque (no UTF-8 validation — see non-goals).

**Performance note:** the combinator string body is slower than today's opaque
`takeStringBody` scan, which shows up on the string-heavy `twitter.json`. Measure after
correctness. Only if it regresses materially, replace the hot path with a specialized total
scanner (in the spirit of the library's existing `scanStrFwd`) that validates as it scans.
Optimize the string path, nothing else, and only on evidence.

### value

First-byte `dispatch` (as today) after `ws`, routing to object / array / string / keyword /
number by leading byte, else fail. Arrays/objects fold elements with `foldMany` over an
always-consuming `, element`, same shape as the current parser.

## Conformance harness

### Corpus (vendored)

Vendor `nst/JSONTestSuite` `test_parsing/*.json` (~318 files, MIT) under
`test/jsontestsuite/`, with a `test/jsontestsuite/LICENSE` and an attribution line naming the
upstream commit. Vendoring keeps CI offline and deterministic (the repo already treats
network access in CI as flaky). `test_transform/` is out of scope.

### Runner: one exe, dual mode

New `lake exe conformance`, one parse function, two entry behaviors:

- **Batch / CI mode** (no file arg): walk `test/jsontestsuite/`, classify each file by
  prefix, print a summary, exit nonzero on any regression. Summary line:
  `y: N/N accepted · n: M/M rejected · i: a accepted / r rejected · excluded: e`.
- **Protocol mode** (`conformance <file>`): read the file, run `json`, exit **0** on accept,
  **1** on reject. This is grip's JSONTestSuite `parsers/` entry (crash/timeout surface as a
  nonzero-and-not-1 exit naturally).

### Policy lists (explicit, commented)

Two lists live in the runner source, each entry with a one-line reason:

- **`nAllowAccept`** — the invalid-UTF-8 `n_*` files grip accepts under the grammar-strict
  ceiling. Expected, not failures. Shrinking this list later (UTF-8 upgrade) is a strict
  improvement.
- **`excluded`** — pathological deep-nesting `n_*` files that could overflow the process.
  Skipped with a printed note; counted in `excluded: e`. Not run, so they cannot crash CI.

Gate: exit nonzero if any `y_*` is rejected, or any `n_*` outside `nAllowAccept ∪ excluded`
is accepted. `i_*` verdicts are recorded and printed, never gated.

### CI

Build and run `conformance` (batch mode) as a step in the existing `core` job (reuses its
elan + `.lake` cache). A regression fails the build. No new job, no network.

### Official-driver infra (opt-in, not CI)

- `parsers/test_grip.sh` — the wrapper shim invoking the built `conformance` binary in
  protocol mode, plus a README snippet giving the exact `programs`-dict entry to register
  grip in upstream `run_tests.py`.
- `test/run-jsontestsuite.sh` — clones `nst/JSONTestSuite` into a git-ignored scratch dir,
  injects grip's entry into a *copy* of `run_tests.py` (never edits the upstream checkout),
  runs it restricted to grip, and emits grip's per-file verdicts / HTML column. Requires no
  other language toolchain. `.gitignore` gets the scratch path.
- We never PR the entry upstream (standing rule); it lives in grip's repo, fork-ready.

Value: grip's verdicts come from the *canonical* driver, and the official verdicts must agree
with our Lean runner — a cross-check on both.

## Benchmark revamp (`bench/Bench.lean`, `bench/RESULTS.md`)

- The grip row now measures the **strict** parser (honest; likely a few ms slower on
  string-heavy `twitter`/`citm`).
- **Strict-match the two in-repo Lean baselines** (`StdParsecJson`, `HandScanner`) to the
  same RFC grammar, so `grip vs Std.Parsec` and `grip vs runtime-floor` stay genuinely
  same-task and isolate combinator overhead from validation overhead.
- **nom / attoparsec stay loose** (shape-only scanners), relabeled in RESULTS as such and
  disclosed as *conservative for grip*: a strict competitor would only be slower, narrowing
  the gap. All parsers still return `count=111130` on the valid benchmark files.
- Rewrite the RESULTS narrative from "loose leaf-counter, identical count" to "grip fully
  validates RFC-8259 — here is its JSONTestSuite conformance **and** its throughput," with a
  conformance-score table alongside the throughput table.

## Files

Touched:

- `examples/Json.lean` — rewrite to grammar-strict; add local `eof`.
- `test/Test.lean` — update `#guard`s to strict semantics (e.g. `[truue]` now rejects).
- `test/Conformance.lean` — new dual-mode runner.
- `test/jsontestsuite/` — vendored corpus + LICENSE/attribution.
- `parsers/test_grip.sh` (+ README snippet) — JSONTestSuite `parsers/` entry.
- `test/run-jsontestsuite.sh` — opt-in official-driver harness.
- `bench/Bench.lean` — strict-match `StdParsecJson` and `HandScanner`.
- `bench/RESULTS.md` — rewrite narrative + conformance table.
- `lakefile.toml` — add the `conformance` exe.
- `.github/workflows/ci.yml` — build + run `conformance` in the `core` job.
- `.gitignore` — scratch clone dir.

Untouched: grip core library (`Grip/`), `grip-props/`.

## Test / verification strategy

- Test-driven against the vendored corpus: the `y_*`/`n_*` verdicts are the acceptance
  oracle for the parser. Build the parser to make the batch runner green.
- Keep the `#guard` smoke tests in `test/Test.lean`, updated for strict semantics, as fast
  compile-time checks independent of the corpus.
- Cross-check: the Lean runner's verdicts and the official `run_tests.py` verdicts for grip
  must agree.
- Benchmark files are valid JSON, so strict and loose parsers must still all report
  `count=111130` on `canada`; a divergence is a bug.

## Risks

- **Backtracking semantics** (number/string) — the main correctness risk; mitigated by TDD
  against `n_number_*` / `n_string_*`.
- **twitter throughput regression** from the validating string body — mitigated by the
  measure-then-specialize plan; acceptable as a known cost if small.
- **Deep-nesting crash** — contained by the `excluded` list; a documented non-goal.
