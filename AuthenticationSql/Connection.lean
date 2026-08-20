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
-/
structure SqlConnection (m : Type → Type) where
  query : String → Array SqlValue → m (Array SqlRow)
  exec : String → Array SqlValue → m Nat
  transaction : {α : Type} → m α → m α

namespace SqlConnection

variable {m : Type → Type} [Functor m] (conn : SqlConnection m) (d : Dialect) (s : Statement)

def rows : m (Array SqlRow) :=
  let (text, params) := s.render d
  conn.query text params

def affected : m Nat :=
  let (text, params) := s.render d
  conn.exec text params

def first : m (Option SqlRow) :=
  (fun rows => rows[0]?) <$> conn.rows d s

end SqlConnection

end Authentication.Sql
