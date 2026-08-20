/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import AuthenticationPostgres
import AuthenticationSqlite

/-!
The dialect seam (AUTH-15.2.2).

The conformance suite is what says the shared statements are right; these checks are about the
seam itself, which the conformance suite cannot reach while only one backend runs.
-/

namespace Tests.Sql
open Authentication.Sql

/--
Parameters are numbered by their position among parameters, not among fragments. A statement
built by appending therefore numbers its parameters as though it had been written in one piece,
which is what lets the shared statements be assembled from a `SELECT` and a `WHERE`.
-/
theorem renderFrom_append (d : Dialect) (next : Nat) (fs gs : List Fragment) :
    Statement.renderFrom d next (fs ++ gs)
      = Statement.renderFrom d next fs
        ++ Statement.renderFrom d (next + Statement.paramCount fs) gs := by
  induction fs generalizing next with
  | nil => simp [Statement.renderFrom, Statement.paramCount]
  | cons f fs ih =>
    cases f <;>
      simp [Statement.renderFrom, Statement.paramCount, ih, String.append_assoc,
        Nat.add_assoc, Nat.add_comm]

/-- The consequence that matters at a call site: appending a parameter gives it the next number,
whatever mixture of text and table names precedes it. -/
theorem placeholder_of_appended_param (d : Dialect) (fs : List Fragment) (v : SqlValue) :
    Statement.renderFrom d 1 (fs ++ [.param v])
      = Statement.renderFrom d 1 fs ++ d.placeholder (1 + Statement.paramCount fs) := by
  simp [renderFrom_append, Statement.renderFrom]

private def sample : Statement :=
  sql!"SELECT id FROM {(⟨"attempts"⟩ : TableName)}
       WHERE tenant = {("acme" : String)} AND failed_entries = {(3 : Int)}"

private def occurs (needle haystack : String) : Bool := (haystack.splitOn needle).length > 1

/-- Each backend's schema has to create the tables the shared statements name, under the
qualification its own dialect applies. A table renamed on one side and not the other is
otherwise found only when that statement first runs. -/
private def schemaCoversTables (dialect : Dialect) (ddl : String) : Bool :=
  tableNames.all fun name => occurs (dialect.table name) ddl

def checks : List (String × Bool) :=
  let (postgresText, postgresParams) := sample.render Authentication.Postgres.dialect
  let (sqliteText, sqliteParams) := sample.render Authentication.Sqlite.dialect
  [ ("sql: the Postgres dialect qualifies tables with the schema and numbers from $1",
      occurs "FROM auth.attempts" postgresText && occurs "tenant = $1" postgresText
        && occurs "failed_entries = $2" postgresText),
    ("sql: the SQLite dialect prefixes tables and numbers from ?1",
      occurs "FROM auth_attempts" sqliteText && occurs "tenant = ?1" sqliteText
        && occurs "failed_entries = ?2" sqliteText),
    ("sql: a parameter's value never reaches the statement text",
      !occurs "acme" postgresText && !occurs "acme" sqliteText),
    ("sql: the values bound do not depend on the dialect",
      postgresParams == sqliteParams
        && postgresParams == #[SqlValue.text "acme", SqlValue.int 3]),
    ("sql: the Postgres schema creates every table the statements name",
      schemaCoversTables Authentication.Postgres.dialect Authentication.Postgres.createSchemaSql),
    ("sql: the SQLite schema creates every table the statements name",
      schemaCoversTables Authentication.Sqlite.dialect Authentication.Sqlite.createSchemaSql) ]

/-! ## The connection a transaction runs on -/

/-- A driver that hands out a different connection every time it is asked, which is what a pool
does. Neither shipped backend can exercise this: with one pinned connection, a transaction spread
over several looks exactly like one that was not. -/
private structure Pool where
  next : IO.Ref Nat
  log : IO.Ref (List (Nat × String))

private def Pool.borrow (pool : Pool) : IO Nat := pool.next.modifyGet fun n => (n, n + 1)

private def Pool.record (pool : Pool) (conn : Nat) (text : String) : IO Unit :=
  pool.log.modify (· ++ [(conn, text)])

/-- The handle is the borrowed connection, and `none` is one not yet chosen: a statement outside
a transaction borrows its own, and a statement inside is given the one the `BEGIN` ran on. -/
private def poolConnection (pool : Pool) : SqlConnection IO where
  handle := (none : Option Nat)
  query handle text _ := do
    pool.record (← handle.getDM pool.borrow) text
    pure #[]
  exec handle text _ := do
    pool.record (← handle.getDM pool.borrow) text
    pure 1
  runTransaction _ action := do
    let borrowed ← pool.borrow
    pool.record borrowed "BEGIN"
    let result ← action (some borrowed)
    pool.record borrowed "COMMIT"
    pure result

def poolChecks : IO (List (String × Bool)) := do
  let pool : Pool := { next := ← IO.mkRef 1, log := ← IO.mkRef [] }
  let store := sqlAuthStore Authentication.Sqlite.dialect (poolConnection pool)
  let tenant : Authentication.TenantId := ⟨"acme"⟩
  store.deleteTenant tenant
  let inside ← pool.log.get
  pool.log.set []
  let _ ← store.auditEntries tenant
  let _ ← store.auditEntries tenant
  let outside ← pool.log.get
  let opened := inside.head?.map (·.1)
  pure
    [ ("sql: a transaction is a BEGIN, the statements it wraps, and a COMMIT",
        inside.length > 3 && (inside.head?.map (·.2)) == some "BEGIN"
          && (inside.getLast?.map (·.2)) == some "COMMIT"),
      ("sql: every statement inside a transaction runs on the connection it was opened on",
        inside.all fun (conn, _) => some conn == opened),
      ("sql: a statement outside a transaction is self-contained on its own connection",
        match outside.map (·.1) with
        | [first, second] => first != second
        | _ => false) ]

end Tests.Sql
