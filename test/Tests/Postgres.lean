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
open Authentication Authentication.Sql

def conninfo : IO String := do
  pure ((← IO.getEnv "AUTHENTICATION_POSTGRES").getD
    "dbname=leanauthentication user=leanauthentication")

private def reported (label : String) (run : IO (List Store.Conformance.Check)) :
    IO (List (String × Bool)) := do
  match ← run.toBaseIO with
  | .ok results => pure (results.map fun check => (s!"{label}: {check.name}", check.passed))
  | .error e => pure [(s!"{label}: the reference backend was reachable ({e})", false)]

def conformanceChecks : IO (List (String × Bool)) :=
  reported "postgres" do
    let connection ← Authentication.Postgres.connect (← conninfo)
    Authentication.Postgres.createSchema connection
    Store.Conformance.run (Authentication.Postgres.store connection) "postgres"

/-- The same suite over a pool, which reaches the other driver adapter without restating a single
one of the guarantees it checks. -/
def poolConformanceChecks : IO (List (String × Bool)) :=
  reported "postgres pool" do
    let pool ← _root_.Postgres.Pool.create (← conninfo) 2
    pool.withConn (_root_.Postgres.execScript · Authentication.Postgres.createSchemaSql)
    Store.Conformance.run
      (sqlAuthStore Authentication.Postgres.dialect (Authentication.Postgres.poolConnection pool))
      "postgres-pool"

private def backendPid (conn : SqlConnection IO) : IO String := do
  let rows ← conn.query conn.handle "SELECT pg_backend_pid()" #[]
  pure ((rows[0]?).map (·.text 0) |>.getD "")

/--
Which connection a pooled statement lands on, which the conformance suite cannot see: every
guarantee it checks holds whether or not a transaction was spread over several connections.

The pool holds two, so a statement issued while a transaction has one of them can be answered by
the other rather than waiting for the transaction to end. That second connection is what makes
the check meaningful: a `runTransaction` that returned its borrow before running the block would
still see one pid throughout, because the pool hands back the connection most recently returned.
-/
def poolTransactionChecks : IO (List (String × Bool)) := do
  match ← (do
      let pool ← _root_.Postgres.Pool.create (← conninfo) 2
      let conn := Authentication.Postgres.poolConnection pool
      conn.transaction fun inTransaction => do
        let first ← backendPid inTransaction
        let second ← backendPid inTransaction
        pure (first, second, ← backendPid conn)).toBaseIO with
  | .ok (first, second, elsewhere) =>
    pure
      [ ("postgres pool: every statement inside a transaction runs on one connection",
          first != "" && first == second),
        ("postgres pool: a statement given no connection borrows one of its own",
          elsewhere != "" && elsewhere != first) ]
  | .error e => pure [(s!"postgres pool: the transaction ran ({e})", false)]

end Tests.Postgres
