/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lake
open System Lake DSL

package authentication where
  version := v!"0.1.0"
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩,
    ⟨`warningAsError, true⟩]

require leansqlite from git
  "https://github.com/leanprover/leansqlite" @ "v4.33.0"

require leanpostgres from git
  "https://github.com/paulbutcher/leanpostgres" @ "v0.4.0"

require leancurl from git
  "https://github.com/paulbutcher/leancurl" @ "v0.1.0"

require leancrypto from git
  "https://github.com/paulbutcher/leancrypto" @ "v0.1.0"

@[default_target]
lean_lib Authentication

@[default_target]
lean_lib AuthenticationSql

@[default_target]
lean_lib AuthenticationSqlite

@[default_target]
lean_lib AuthenticationPostgres

@[default_target]
lean_lib AuthenticationPostmark

/--
Tests live in the `test/` subproject rather than here, so that a project depending on this one is
free to name its own modules `Tests.*` and acquires nothing this library does not ship.
-/
@[test_driver]
script tests (args) do
  let pkg ← getRootPackage
  let child ← IO.Process.spawn {
    cmd := "lake"
    args := #["test", "--"] ++ args.toArray
    cwd := pkg.dir / "test"
  }
  child.wait
