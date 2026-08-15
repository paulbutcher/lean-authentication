/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
Statements as data, rendered against a dialect (AUTH-15.2.2).

A statement is a list of fragments. A value can enter a statement only as `Fragment.param`, and
`renderFrom` emits a placeholder for it rather than its contents, so no path exists by which a
value reaches the SQL text. That is a property of the types, not of the care taken at each call
site, which is what makes one shared set of statements safe to write once.
-/

namespace Authentication.Sql

/--
What the two SQL backends disagree about. It is this small because the workload was chosen to
keep it small: timestamps are epoch integers rather than a database timestamp type
(AUTH-15.7.4), and `INSERT ... ON CONFLICT DO NOTHING` and `RETURNING` are spelled the same in
both. What is left is how a parameter is written and where the objects live.
-/
structure Dialect where
  /-- One-based, matching the numbering `renderFrom` assigns. -/
  placeholder : Nat → String
  /-- Maps a bare table name to the qualified name that backend's schema uses. -/
  table : String → String

/-- Text, integers, and null are the whole of what this schema stores. -/
inductive SqlValue where
  | null
  | text (value : String)
  | int (value : Int)
  deriving Repr, BEq, Inhabited

inductive Fragment where
  | text (value : String)
  | table (name : String)
  | param (value : SqlValue)
  deriving Repr, BEq, Inhabited

class ToFragment (α : Type) where
  toFragment : α → Fragment

/-- Wraps a bare table name so that interpolating it is a name and not a parameter. -/
structure TableName where
  value : String
  deriving Repr, BEq

instance : ToFragment TableName where toFragment t := .table t.value
instance : ToFragment String where toFragment s := .param (.text s)
instance : ToFragment Int where toFragment i := .param (.int i)
instance : ToFragment Nat where toFragment n := .param (.int n)
instance : ToFragment Bool where toFragment b := .param (.int (if b then 1 else 0))

instance {α : Type} [ToFragment α] : ToFragment (Option α) where
  toFragment
    | none => .param .null
    | some a => ToFragment.toFragment a

structure Statement where
  fragments : List Fragment
  deriving Repr, BEq, Inhabited

instance : Append Statement where
  append s t := ⟨s.fragments ++ t.fragments⟩

namespace Statement

def paramCount : List Fragment → Nat
  | [] => 0
  | .param _ :: rest => paramCount rest + 1
  | _ :: rest => paramCount rest

def params : List Fragment → Array SqlValue
  | [] => #[]
  | .param v :: rest => #[v] ++ params rest
  | _ :: rest => params rest

/-- `next` is the number the following parameter will be given. -/
def renderFrom (d : Dialect) (next : Nat) : List Fragment → String
  | [] => ""
  | .text v :: rest => v ++ renderFrom d next rest
  | .table t :: rest => d.table t ++ renderFrom d next rest
  | .param _ :: rest => d.placeholder next ++ renderFrom d (next + 1) rest

def render (d : Dialect) (s : Statement) : String × Array SqlValue :=
  (renderFrom d 1 s.fragments, params s.fragments)

end Statement

open Lean in
/--
Builds a statement from interpolated SQL. Interpolations become fragments through `ToFragment`,
so a table name interpolates as a name and everything else as a parameter.
-/
syntax:max "sql!" interpolatedStr(term) : term

macro_rules
  | `(sql! $s) => do
    let mut parts := #[]
    for chunk in s.raw.getArgs do
      if let some lit := chunk.isInterpolatedStrLit? then
        parts := parts.push (← `(Authentication.Sql.Fragment.text $(Lean.quote lit)))
      else
        parts := parts.push (← `(Authentication.Sql.ToFragment.toFragment $(⟨chunk⟩)))
    `(Authentication.Sql.Statement.mk [$(parts),*])

end Authentication.Sql
