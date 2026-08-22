/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import AuthenticationPostgres.Schema
public import Postgres
import AuthenticationSql

/-!
The Postgres backend, the reference one (AUTH-15.8.1).

What is here is a driver adapter. The statements, the conditional updates, and the encoding of
every value are the shared ones (AUTH-15.2.2), so this backend and the SQLite backend differ in
what the conformance suite can observe only if the driver or the schema is wrong.

Parameters go to the server as text and come back as text, which is libpq's default and costs
nothing here: every column in the schema is text or a `bigint` epoch second, and the shared
decoders already read an integer from either representation.
-/

public section

namespace Authentication.Postgres

open Authentication.Sql

/--
A connection and the transaction nesting it is inside. Postgres treats a second `BEGIN` as a
no-op and warns, and the `COMMIT` that follows would end the outer transaction early, so the
depth is tracked rather than discovered.
-/
structure Connection where
  conn : Postgres.Conn
  private depth : IO.Ref Nat

/--
Opens a connection. An empty `conninfo` leaves it to libpq's own defaults and the `PG*`
environment variables.
-/
def connect (conninfo : String := "") : IO Connection := do
  pure { conn := ← Postgres.«open» conninfo, depth := ← IO.mkRef 0 }

def createSchema (c : Connection) : IO Unit := Postgres.execScript c.conn createSchemaSql

/-! ## The driver adapter -/

private def bind (stmt : Postgres.Stmt) (params : Array SqlValue) : IO Unit := do
  let mut position : Int32 := 1
  for value in params do
    match value with
    | .null => stmt.bindNull position
    | .text text => stmt.bindText position text
    | .int number => stmt.bindText position (toString number)
    position := position + 1

private def readRow (stmt : Postgres.Stmt) (columns : Nat) : IO SqlRow := do
  let mut row : SqlRow := #[]
  for index in [0 : columns] do
    let position := Int32.ofNat index
    row := row.push <| ←
      if ← stmt.columnIsNull position then pure .null
      else do pure (.text (← stmt.columnText position))
  pure row

private def prepared (conn : Postgres.Conn) (text : String) (params : Array SqlValue) :
    IO Postgres.Stmt := do
  let stmt ← Postgres.prepare conn text
  bind stmt params
  pure stmt

private def runQuery (conn : Postgres.Conn) (text : String) (params : Array SqlValue) :
    IO (Array SqlRow) := do
  let stmt ← prepared conn text params
  let mut rows : Array SqlRow := #[]
  let mut columns := 0
  while ← stmt.step do
    if rows.isEmpty then
      columns ← stmt.columnCount
    rows := rows.push (← readRow stmt columns)
  pure rows

private def runExec (conn : Postgres.Conn) (text : String) (params : Array SqlValue) : IO Nat := do
  let stmt ← prepared conn text params
  discard stmt.step
  pure ((← stmt.commandTuples).getD 0).toNatClampNeg

/-- An operation reached from inside `runInTx` joins the transaction already open, which is what
the SQLite backend does too, so a client sees one behaviour from both. -/
private def withTransaction {α : Type} (c : Connection) (action : IO α) : IO α := do
  if (← c.depth.get) > 0 then
    action
  else
    c.depth.set 1
    try
      let result ← _root_.Postgres.transaction c.conn action
      c.depth.set 0
      pure result
    catch e =>
      c.depth.set 0
      throw e

def connection (c : Connection) : SqlConnection IO where
  handle := c
  query c text params := runQuery c.conn text params
  exec c text params := runExec c.conn text params
  -- There is one connection and its depth is tracked on it, so the block is handed the one the
  -- `BEGIN` ran on, which is the one it was already going to use.
  runTransaction c action := withTransaction c (action c)

/-- Runs `action` on the handle's connection if it has one, and on a connection borrowed for the
length of `action` if it does not. -/
private def borrowing {α : Type} (pool : Postgres.Pool) (handle : Option Postgres.Conn)
    (action : Postgres.Conn → IO α) : IO α :=
  match handle with
  | some conn => action conn
  | none => pool.withConn action

/--
The same adapter over a pool, for a client that already keeps one and would rather authentication
drew from it than held a connection of its own.

The handle is the connection a statement has been given, and `none` is a statement that has not
been given one: it borrows for its own duration and returns what it borrowed. `runTransaction`
borrows once and holds it, so the `BEGIN`, the statements between and the `COMMIT` all reach the
one connection; a transaction reached from inside another joins it rather than nesting, as
`connection` does.

Borrowing blocks the calling thread until the pool has a connection free, because the ports this
library is written against are `IO` and there is no `Async` here to suspend on instead. A caller
on a fiber-scheduled server therefore gives up the thread it shares with every other request in
flight for as long as the borrow lasts, which for a transaction is the whole of it.
-/
def poolConnection (pool : Postgres.Pool) : SqlConnection IO where
  handle := (none : Option Postgres.Conn)
  query handle text params := borrowing pool handle (runQuery · text params)
  exec handle text params := borrowing pool handle (runExec · text params)
  runTransaction handle action :=
    match handle with
    | some conn => action (some conn)
    | none => pool.withConn fun conn => _root_.Postgres.transaction conn (action (some conn))

/-- The port, wired to one connection. -/
def store (c : Connection) : AuthStore IO := sqlAuthStore dialect (connection c)

/--
The transactional capability, which the reference backend has to supply (AUTH-15.8.1). The
block runs against the same connection, which is the price AUTH-15.3.5 requires be stated: the
library's tables live in the client's own database.
-/
def transactionalStore (c : Connection) : TransactionalStore IO :=
  sqlTransactionalStore dialect (connection c)

end Authentication.Postgres
