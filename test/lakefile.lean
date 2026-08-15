/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lake
open Lake DSL

require authentication from ".."

package «authentication-test» where
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩,
    ⟨`warningAsError, true⟩]

/-- Claiming the whole `Tests` namespace is safe here because nothing depends on this package,
and it means a test file that nothing imports is still compiled. -/
@[default_target]
lean_lib Tests where
  globs := #[`Tests.*]

@[default_target, test_driver]
lean_exe tests where
  root := `Tests.Main
