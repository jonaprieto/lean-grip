import Lake
open Lake DSL

package «grip» where
  version := v!"0.3.6"
  -- Every binder explicit; the graded core relies on no auto-bound implicits.
  leanOptions := #[⟨`autoImplicit, false⟩, ⟨`relaxedAutoImplicit, false⟩]

require batteries from git
  "https://github.com/leanprover-community/batteries" @ "v4.33.0"

-- API documentation (doc-gen4) is dev-only: build with `lake -Kenv=dev build Grip:docs`.
-- Gated behind `-Kenv=dev` so a plain `require grip` never pulls it into the dependency
-- closure; the core stays batteries-only. Pinned to the Lean v4.33.1 release.
meta if get_config? env = some "dev" then
require «doc-gen4» from git
  "https://github.com/leanprover/doc-gen4" @ "v4.33.1"

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
