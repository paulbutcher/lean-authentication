/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lake
open System Lake DSL

package authentication where
  version := v!"0.16.3"
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩,
    ⟨`warningAsError, true⟩]

require json from git
  "https://github.com/paulbutcher/lean-json" @ "v0.3.0"

require leansqlite from git
  "https://github.com/leanprover/leansqlite" @ "v4.33.0"

require leanpostgres from git
  "https://github.com/paulbutcher/leanpostgres" @ "v0.7.3"

require leancurl from git
  "https://github.com/paulbutcher/leancurl" @ "v0.3.1"

require leancrypto from git
  "https://github.com/paulbutcher/leancrypto" @ "v0.4.1"

/-
The one dependency needing a system library, `pkg-config` and OpenSSL 3 development headers. It is
confined to the federation targets (AUTH-6.11), so a consumer taking the magic link flow, either
SQL backend, or the authorisation server links none of it.
-/
require «lean-libcrypto» from git
  "https://github.com/paulbutcher/lean-libcrypto" @ "v0.2.0"

/-
JOSE, and the backend that gives it the elliptic curve half. `lean-jose` is pure Lean and holds the
algorithm allowlist in its `Policy`, so a token never selects the means of its own verification
(AUTH-6.5); `jose-libcrypto` supplies ES256 and the private key operations, over the binding below.
-/
require jose from git
  "https://github.com/paulbutcher/lean-jose" @ "v0.2.1"

require «jose-libcrypto» from git
  "https://github.com/paulbutcher/jose-libcrypto" @ "v0.1.1"

require leanaws from git
  "https://github.com/paulbutcher/lean-aws" @ "v0.3.1"

/-
The HTTP integration target's dependencies, and only its (AUTH-2.3). `lean-forms` and `lean-htmx`
are not among them: `Middleware.params` already decodes a form body, and nothing these routes do
needs a partial page update.
-/
require routing from git
  "https://github.com/paulbutcher/lean-routing" @ "v0.7.2"

require html from git
  "https://github.com/paulbutcher/lean-html" @ "v0.9.0"

require middleware from git
  "https://github.com/paulbutcher/lean-middleware" @ "v0.13.0"

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

/-- The authorisation server (§20). It needs no `require` of its own: percent-encoding comes
from `Std.Http`, which the toolchain ships, and everything else it uses is already here. -/
@[default_target]
lean_lib AuthenticationOAuth

/-- The federated sign-in protocol and the secrets it needs (AUTH-6.11). It is the target that
links OpenSSL, which is why it is its own and why the routes are not in `AuthenticationHttp`. -/
@[default_target]
lean_lib AuthenticationOidc

/-- The outbound fetch of AUTH-6.11, and only that: it knows nothing of OIDC or of the
authorisation server, so either may be wired to it without depending on the other. -/
@[default_target]
lean_lib AuthenticationFetch

/-- The federated sign-in routes (AUTH-6.11). Separate from `AuthenticationHttp` because mounting
these means linking OpenSSL, and mounting those must not. -/
@[default_target]
lean_lib AuthenticationOidcHttp

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
