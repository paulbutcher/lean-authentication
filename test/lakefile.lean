/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lake
open Lake DSL

require authentication from ".."

require «routing-std» from git
  "https://github.com/paulbutcher/lean-routing" @ "v0.15.2" / "std"

package «authentication-test» where
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩,
    ⟨`warningAsError, true⟩]

/-- The fixtures the tests embed with `include_str`. Declared as an input so that regenerating one
rebuilds the module reading it: Lake traces a module by its own content, so without this the old
bytes stay compiled in and a regenerated fixture is silently not used. -/
input_dir fixtures where
  path := "fixtures"
  text := true

/-- The documentation, and the examples its code blocks are checked against, embedded by
`Tests.Docs` for the reason `fixtures` is declared. -/
input_dir docs where
  path := "../docs"
  text := true

input_dir docExamples where
  path := "Tests/Docs"
  text := true

/-- Claiming the whole `Tests` namespace is safe here because nothing depends on this package,
and it means a test file that nothing imports is still compiled. -/
@[default_target]
lean_lib Tests where
  globs := #[`Tests.*]
  needs := #[fixtures, docs, docExamples]

@[default_target, test_driver]
lean_exe tests where
  root := `Tests.Main
