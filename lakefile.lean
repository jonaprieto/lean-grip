import Lake
open Lake DSL

package «grip» where
  -- Every binder explicit; the graded core relies on no auto-bound implicits.
  leanOptions := #[⟨`autoImplicit, false⟩, ⟨`relaxedAutoImplicit, false⟩]

require batteries from git
  "https://github.com/leanprover-community/batteries" @ "v4.28.0"

-- API documentation (doc-gen4) is dev-only: build with `lake -Kenv=dev build Grip:docs`.
-- Gated behind `-Kenv=dev` so a plain `require grip` never pulls it into the dependency
-- closure; the core stays batteries-only. Pinned to the doc-gen4 commit on Lean v4.28.0.
meta if get_config? env = some "dev" then
require «doc-gen4» from git
  "https://github.com/leanprover/doc-gen4" @ "a41d5ebebfa77afe737fec8de8ad03fc8b08fdff"

@[default_target]
lean_lib «Grip» where
  -- Build every module under Grip/, not just what the root re-exports, so no submodule
  -- can hide unbuilt (and untested) behind a missing import.
  globs := #[.andSubmodules `Grip]

lean_lib «Examples» where
  srcDir := "examples"
  globs := #[.one `Json, .one `Sexp, .one `Lambda, .one `Http, .one `Toml, .one `Yaml]

lean_lib «Test» where
  srcDir := "test"

lean_exe «bench» where
  root := `Bench
  srcDir := "bench"

lean_exe «conformance» where
  root := `Conformance
  srcDir := "test"
