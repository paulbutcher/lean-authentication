/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import AuthenticationPostgres

/-!
The shipped conformance suite, run against the reference backend (AUTH-15.5.2, AUTH-15.8.1).

This one needs a server, so unlike the SQLite run it can fail for reasons that are nothing to do
with the library. It reports that as a failure rather than a skip: a suite that quietly passes
when the reference backend was never reached is worse than no suite.

`AUTHENTICATION_POSTGRES` overrides the connection; otherwise libpq's own defaults and the `PG*`
environment variables apply.
-/

namespace Tests.Postgres
open Authentication

def conninfo : IO String := do
  pure ((← IO.getEnv "AUTHENTICATION_POSTGRES").getD
    "dbname=leanauthentication user=leanauthentication")

def conformanceChecks : IO (List (String × Bool)) := do
  match ← (do
      let connection ← Authentication.Postgres.connect (← conninfo)
      Authentication.Postgres.createSchema connection
      Store.Conformance.run (Authentication.Postgres.store connection) "postgres").toBaseIO with
  | .ok results => pure (results.map fun check => (s!"postgres: {check.name}", check.passed))
  | .error e => pure [(s!"postgres: the reference backend was reachable ({e})", false)]

end Tests.Postgres
