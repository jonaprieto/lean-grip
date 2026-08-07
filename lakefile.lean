import Lake
open Lake DSL

package «grip» where
  version := v!"0.1.0"
  -- Every binder explicit; the graded core relies on no auto-bound implicits.
  leanOptions := #[⟨`autoImplicit, false⟩, ⟨`relaxedAutoImplicit, false⟩]

require batteries from git
  "https://github.com/leanprover-community/batteries" @ "v4.32.2"

-- API documentation (doc-gen4) is dev-only: build with `lake -Kenv=dev build Grip:docs`.
-- Gated behind `-Kenv=dev` so a plain `require grip` never pulls it into the dependency
-- closure; the core stays batteries-only. Pinned to the doc-gen4 commit on Lean v4.32.
meta if get_config? env = some "dev" then
require «doc-gen4» from git
  "https://github.com/leanprover/doc-gen4" @ "092d6318789e7bb9160ade1e85bdbcc0abfd7f6e"

@[default_target]
lean_lib «Grip» where
  -- Build every module under Grip/, not just what the root re-exports, so no submodule
  -- can hide unbuilt (and untested) behind a missing import.
  globs := #[.andSubmodules `Grip]

lean_lib «Examples» where
  srcDir := "examples"
  globs := #[.one `Sexp, .one `Lambda, .one `Http, .one `Toml, .one `Yaml]

lean_lib «Test» where
  srcDir := "test"

lean_exe «bench» where
  root := `Bench
  srcDir := "bench"
