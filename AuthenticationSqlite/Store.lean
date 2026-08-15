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

def createSchemaSql : String := "
    CREATE TABLE IF NOT EXISTS auth_accounts (
      tenant TEXT NOT NULL,
      id TEXT NOT NULL,
      identity_local TEXT NOT NULL,
      identity_domain TEXT NOT NULL,
      sending_local TEXT NOT NULL,
      sending_domain TEXT NOT NULL,
      status TEXT NOT NULL,
      created_at INTEGER NOT NULL,
      PRIMARY KEY (tenant, id),
      UNIQUE (tenant, identity_local, identity_domain)
    );
    CREATE TABLE IF NOT EXISTS auth_account_emails (
      tenant TEXT NOT NULL,
      account_id TEXT NOT NULL,
      local TEXT NOT NULL,
      domain TEXT NOT NULL,
      PRIMARY KEY (tenant, account_id, local, domain)
    );
    CREATE TABLE IF NOT EXISTS auth_attempts (
      tenant TEXT NOT NULL,
      id TEXT NOT NULL,
      address_local TEXT NOT NULL,
      address_domain TEXT NOT NULL,
      identity_local TEXT NOT NULL,
      identity_domain TEXT NOT NULL,
      phase TEXT NOT NULL,
      magic_key TEXT NOT NULL,
      magic_bytes TEXT NOT NULL,
      code_key TEXT NOT NULL,
      code_bytes TEXT NOT NULL,
      emailed_key TEXT,
      emailed_bytes TEXT,
      nonce_key TEXT NOT NULL,
      nonce_bytes TEXT NOT NULL,
      failed_entries INTEGER NOT NULL,
      expires_at INTEGER NOT NULL,
      requester_ip TEXT,
      requester_agent TEXT,
      requester_location TEXT,
      invitation_id TEXT,
      PRIMARY KEY (tenant, id)
    );
    CREATE UNIQUE INDEX IF NOT EXISTS auth_attempts_live
      ON auth_attempts (tenant, identity_local, identity_domain)
      WHERE phase IN ('pending', 'revealed');
    CREATE TABLE IF NOT EXISTS auth_sessions (
      tenant TEXT NOT NULL,
      id TEXT NOT NULL,
      account_id TEXT NOT NULL,
      digest_key TEXT NOT NULL,
      digest_bytes TEXT NOT NULL,
      created_at INTEGER NOT NULL,
      last_seen_at INTEGER NOT NULL,
      idle_expires_at INTEGER NOT NULL,
      absolute_expires_at INTEGER NOT NULL,
      user_agent TEXT,
      location TEXT,
      revoked_at INTEGER,
      PRIMARY KEY (tenant, id)
    );
    CREATE INDEX IF NOT EXISTS auth_sessions_digest
      ON auth_sessions (tenant, digest_key, digest_bytes);
    CREATE TABLE IF NOT EXISTS auth_invitations (
      tenant TEXT NOT NULL,
      id TEXT NOT NULL,
      address_local TEXT NOT NULL,
      address_domain TEXT NOT NULL,
      token_key TEXT NOT NULL,
      token_bytes TEXT NOT NULL,
      metadata TEXT NOT NULL,
      state TEXT NOT NULL,
      expires_at INTEGER NOT NULL,
      created_by TEXT,
      consumed_at INTEGER,
      PRIMARY KEY (tenant, id)
    );
    CREATE TABLE IF NOT EXISTS auth_audit (
      seq INTEGER PRIMARY KEY AUTOINCREMENT,
      tenant TEXT NOT NULL,
      occurred_at INTEGER NOT NULL,
      actor_ref TEXT,
      kind TEXT NOT NULL,
      subject TEXT NOT NULL,
      detail TEXT NOT NULL
    );
    CREATE INDEX IF NOT EXISTS auth_audit_tenant ON auth_audit (tenant, seq);
  "

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
-/
def openFile (path : System.FilePath) (busyTimeoutMs : Int32 := 5000) : IO SQLite := do
  let db ← SQLite.openWith path .readWriteCreate (busyTimeoutMs := busyTimeoutMs)
  db.exec "PRAGMA journal_mode=WAL"
  createSchema db
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
