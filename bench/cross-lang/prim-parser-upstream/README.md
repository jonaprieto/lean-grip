# Upstream prim-parser benchmark

Validate-and-count on canada.json against the actual upstream prim-parser
(`janmasrovira/prim-parser` main `e1f3f7b`), char-level `List.Vector Char n`. Count-only,
same task as grip, returns 111130.

Distinct from `bench/cross-lang/prim-parser/`, which benchmarks a local byte-level
deep-embedded reimplementation (`research/prim-parser`'s `G` framework) — not upstream.

## Run

```sh
cd bench/cross-lang/prim-parser-upstream && lake exe cache get && lake build && .lake/build/bin/bench-canada
```

Needs network (fetches upstream prim-parser + mathlib) and a mathlib cache. Prints
`count=111130`, `parse_best_ms`, `vector_build_ms`.

## Result (this machine, Lean v4.28.0)

parse ~698 ms, vector-build ~20 ms. grip does the same task in ~19 ms → **~35x faster**.
The cost is the char linked-list input (`List.Vector Char`: boxed chars, no O(1) access,
no bulk scan) and `List`-accumulating `many`/`sepBy`, not the grade machinery.
