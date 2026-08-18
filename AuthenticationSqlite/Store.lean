/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import AuthenticationSql
import SQLite

/-!
The SQLite backend.

It lives in its own target because the core library depends on no driver (AUTH-2.2). What is
here is a schema, a dialect, and an adapter; the statements are the shared ones (AUTH-15.2.2),
so the conditional updates this backend runs are the same text the Postgres backend runs.

Objects are prefixed `auth_` so they cannot collide with the client's own, which is what a
dedicated schema does for Postgres (AUTH-15.7.1).
-/

namespace Authentication.Sqlite

open SQLite Authentication.Sql

/-- SQLite numbers parameters from one, like Postgres, and spells the prefix `?`. -/
def dialect : Dialect where
  placeholder n := s!"?{n}"
  table name := "auth_" ++ name

/-! ## Schema -/

/--
The schema, embedded from the migration files this package ships in `migrations/sqlite` so that
there is one copy of it rather than two that can drift. Applying it to a database that will
outlive the process is the client's (AUTH-15.7.1); what this serves is `openInMemory`, which
starts empty every time.
-/
private def initialSql : String :=
  include_str "../migrations/sqlite/20260818120000_authentication_initial.up.sql"

private def rateCountersSql : String :=
  include_str "../migrations/sqlite/20260818130000_authentication_rate_counters.up.sql"

def createSchemaSql : String := initialSql ++ rateCountersSql

def createSchema (db : SQLite) : IO Unit := db.exec createSchemaSql

/--
Opens an in-memory database with the schema applied. This is what the tests run against, so
they run the statements production runs rather than a parallel implementation (AUTH-16.5).
-/
def openInMemory : IO SQLite := do
  let db ← SQLite.openWith ":memory:" .readWriteCreate
  createSchema db
  pure db


/--
Opens a file-backed database. WAL and a busy timeout are not optional for a SQLite deployment:
without them ordinary concurrent code submissions produce `SQLITE_BUSY` (AUTH-15.8.3).

The schema is not applied here. A database that outlives the process is migrated by the client,
and a library quietly running DDL on every open is what would make the shipped migrations
pointless.
-/
def openFile (path : System.FilePath) (busyTimeoutMs : Int32 := 5000) : IO SQLite := do
  let db ← SQLite.openWith path .readWriteCreate (busyTimeoutMs := busyTimeoutMs)
  db.exec "PRAGMA journal_mode=WAL"
  pure db

/-! ## The driver adapter -/

private def bind (stmt : Stmt) (params : Array SqlValue) : IO Unit := do
  let mut position : Int32 := 1
  for value in params do
    match value with
    | .null => stmt.bindNull position
    | .text text => stmt.bindText position text
    | .int number => stmt.bindInt64 position (Int64.ofInt number)
    position := position + 1

/-- Reads a row as the values the columns hold, without consulting the schema, so a column added
to a `SELECT` needs no instance and no derivation. -/
private def readRow (stmt : Stmt) : IO SqlRow := do
  let mut row : SqlRow := #[]
  for index in [0 : stmt.columnCount.toNat] do
    let position := Int32.ofNat index
    row := row.push <| ←
      match ← stmt.columnType position with
      | .null => pure .null
      | .integer => do pure (.int (← stmt.columnInt64 position).toInt)
      | _ => do pure (.text (← stmt.columnText position))
  pure row

private def prepared (db : SQLite) (text : String) (params : Array SqlValue) : IO Stmt := do
  let stmt ← db.prepare text
  bind stmt params
  pure stmt

def connection (db : SQLite) : SqlConnection IO where
  query text params := do
    let stmt ← prepared db text params
    let mut rows : Array SqlRow := #[]
    while ← stmt.step do
      rows := rows.push (← readRow stmt)
    pure rows
  exec text params := do
    let stmt ← prepared db text params
    while ← stmt.step do
      pure ()
    pure (← db.changes).toNatClampNeg
  -- SQLite has no nested transactions, so an operation reached from inside `runInTx` joins the
  -- transaction already open rather than opening a second one.
  transaction action := do
    if ← db.inTransaction then action else db.transaction action

/-- The port, wired to one connection. -/
def store (db : SQLite) : AuthStore IO := sqlAuthStore dialect (connection db)

/--
The transactional capability (AUTH-15.3). SQLite has no nested transactions, so the block runs
against the same connection: a client that takes this capability accepts that the library's
tables live in its own database (AUTH-15.3.5).
-/
def transactionalStore (db : SQLite) : TransactionalStore IO :=
  sqlTransactionalStore dialect (connection db)

end Authentication.Sqlite
