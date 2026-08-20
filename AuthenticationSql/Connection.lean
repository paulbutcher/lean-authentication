/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import AuthenticationSql.Dialect

/-!
What a driver has to supply for the shared implementation to run on it.

Rendering happens above this seam, so a driver never sees a `Dialect` and never builds SQL. It
receives text it is to prepare and the values it is to bind, in order.
-/

public section

namespace Authentication.Sql

/-- Columns arrive positionally, in the order the statement selected them. -/
abbrev SqlRow := Array SqlValue

namespace SqlRow

def value? (row : SqlRow) (index : Nat) : Option SqlValue := row[index]?

def text? (row : SqlRow) (index : Nat) : Option String :=
  match row.value? index with
  | some (.text v) => some v
  | some (.int v) => some (toString v)
  | _ => none

def text (row : SqlRow) (index : Nat) : String := (row.text? index).getD ""

def int? (row : SqlRow) (index : Nat) : Option Int :=
  match row.value? index with
  | some (.int v) => some v
  | some (.text v) => v.toInt?
  | _ => none

def int (row : SqlRow) (index : Nat) : Int := (row.int? index).getD 0

def nat (row : SqlRow) (index : Nat) : Nat := (row.int index).toNat

end SqlRow

/--
The driver seam. `exec` reports rows affected, which is what the conditional updates read to
decide whether they won (AUTH-15.4.1); a driver that cannot report it cannot implement this
port honestly.

`Handle` is the driver's own notion of one connection, and every operation takes one; the
connection carries the handle to use. A driver holding a single connection makes the handle that
connection, and one drawing from a pool makes it whatever it borrowed. It is a field rather than
a parameter because nothing above this seam has any use for the type.

The handle is what makes `transaction` below safe for a pool: `runTransaction` is handed the one
its `BEGIN` ran on and passes it to the block, so the statements between the `BEGIN` and the
`COMMIT` cannot be issued on a connection chosen separately. That signature is `transaction`'s
rather than this field's because a field of `SqlConnection` may not take a `SqlConnection`: the
occurrence is not strictly positive and the kernel rejects it.
-/
structure SqlConnection (m : Type → Type) where
  {Handle : Type}
  handle : Handle
  query : Handle → String → Array SqlValue → m (Array SqlRow)
  exec : Handle → String → Array SqlValue → m Nat
  runTransaction : {α : Type} → Handle → (Handle → m α) → m α

namespace SqlConnection

variable {m : Type → Type} [Functor m] (conn : SqlConnection m) (d : Dialect) (s : Statement)

def rows : m (Array SqlRow) :=
  let (text, params) := s.render d
  conn.query conn.handle text params

def affected : m Nat :=
  let (text, params) := s.render d
  conn.exec conn.handle text params

def first : m (Option SqlRow) :=
  (fun rows => rows[0]?) <$> conn.rows d s

/-- The same driver, pointed at another of its connections. -/
def on (handle : conn.Handle) : SqlConnection m := { conn with handle }

/--
Runs `action` inside a transaction, handing it a connection scoped to the one the transaction is
open on. A driver with a single connection passes that one and nothing changes for it; a pooled
driver borrows once and passes what it borrowed, which is the only way its `BEGIN`, its
statements and its `COMMIT` reach the same connection.
-/
def transaction {α : Type} (action : SqlConnection m → m α) : m α :=
  conn.runTransaction conn.handle fun handle => action (conn.on handle)

end SqlConnection

end Authentication.Sql
