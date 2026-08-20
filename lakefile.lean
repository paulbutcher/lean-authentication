/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lake
open System Lake DSL

package authentication where
  version := v!"0.2.0"
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩,
    ⟨`warningAsError, true⟩]

require leansqlite from git
  "https://github.com/leanprover/leansqlite" @ "v4.33.0"

require leanpostgres from git
  "https://github.com/paulbutcher/leanpostgres" @ "v0.6.0"

require leancurl from git
  "https://github.com/paulbutcher/leancurl" @ "v0.3.0"

require leancrypto from git
  "https://github.com/paulbutcher/leancrypto" @ "v0.3.0"

require leanaws from git
  "https://github.com/paulbutcher/lean-aws" @ "v0.2.0"

/-
The HTTP integration target's dependencies, and only its (AUTH-2.3). `lean-forms` and `lean-htmx`
are not among them: `Middleware.params` already decodes a form body, and nothing these routes do
needs a partial page update.
-/
require routing from git
  "https://github.com/paulbutcher/lean-routing" @ "v0.7.0"

require html from git
  "https://github.com/paulbutcher/lean-html" @ "v0.7.0"

require middleware from git
  "https://github.com/paulbutcher/lean-middleware" @ "v0.6.0"

/-- The submodules are globbed because `Authentication.Instances` is deliberately not imported by
the root: importing it is what turns the default `Clock` and `RandomBytes` on. -/
@[default_target]
lean_lib Authentication where
  globs := #[.andSubmodules `Authentication]

@[default_target]
lean_lib AuthenticationSql

@[default_target]
lean_lib AuthenticationSqlite

@[default_target]
lean_lib AuthenticationPostgres

@[default_target]
lean_lib AuthenticationPostmark

@[default_target]
lean_lib AuthenticationSes

@[default_target]
lean_lib AuthenticationHttp

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
