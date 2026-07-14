# Cross-library JSON benchmark — shared task spec (every harness MUST match this)

All harnesses implement the *same* task so the comparison is fair. Counts are the correctness
gate: a harness whose counts differ is a different (unfair) task and must be fixed.

## The task: strict RFC-8259 validate + count leaf scalars (NO DOM)

Parse one JSON document and return a leaf count. Do NOT build a value tree / DOM — accumulate an
integer count as you parse.

Counting rule:
- number = 1, string = 1, keyword (`true`/`false`/`null`) = 1
- object KEYS are NOT counted
- arrays and objects contribute 0 for themselves; their count = sum of element/member counts
- top level = one value, then optional whitespace, then END OF INPUT (reject trailing garbage)

## Strict grammar (reject these — do NOT write a loose scanner)

- number: `-? ( 0 | [1-9][0-9]* ) ( . [0-9]+ )? ( [eE] [+-]? [0-9]+ )?`
  reject `00`, `1.`, `1e`, `+1`, a lone `-`, leading zeros.
- string: `"..."`, each element either an unescaped byte `>= 0x20` that is not `"` or `\`,
  or an escape: `\` then one of `" \ / b f n r t`, or `\u` then exactly 4 hex digits.
  Reject unescaped control bytes (`< 0x20`), unknown escapes, short `\u`.
  Do NOT validate UTF-8 beyond this — bytes `>= 0x80` inside strings pass opaque (this matches
  grip's grammar-strict ceiling, so the task is identical).
- keyword: exact `true` / `false` / `null`.
- whitespace between tokens: space 0x20, tab 0x09, LF 0x0A, CR 0x0D.

## Datasets (absolute paths on this machine) and REQUIRED counts

- `/Users/jonaprieto/research/grip/bench/data/canada.json`        -> 111130
- `/Users/jonaprieto/research/grip/bench/data/citm_catalog.json`  -> 16390
- `/Users/jonaprieto/research/grip/bench/data/twitter.json`       -> 11600

CORRECTNESS GATE: your parser MUST produce exactly those counts. If any differs, your
grammar/counting is wrong — fix it before reporting done.

## Implementation quality

Idiomatic, well-written use of the library's OWN combinators. Not a strawman, and not a
hand-rolled byte scanner that bypasses the library — the point is to benchmark the LIBRARY at its
best on this task. No DOM.

## CLI

Accept the dataset path as `argv[1]`; preload it into memory (bytes), parse it best-of-20
in-process (loop 20 times over the preloaded bytes), and print exactly one line:

    <lib> <basename-of-path> count=<n> best_ms=<f>

Use a barrier / `black_box` / volatile so the optimizer cannot elide the parse. Build optimized
(Haskell `-O2`, Rust `--release`, OCaml dune release; flambda if available).

## Timing note

Timing is SECONDARY here: the controller re-measures every harness sequentially (no concurrent
load) for the official numbers. Your job is a correct, idiomatic, strict harness that prints the
right counts and a plausible best_ms. Do not over-tune; do write real optimized code.
