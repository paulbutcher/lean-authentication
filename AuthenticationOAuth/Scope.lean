/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

/-!
Scopes (§20.9).

Opaque strings the host chooses. Nothing here interprets one, and nothing here has a list of
the ones that exist: what a scope permits is the resource server's question, and an
authorisation server that had opinions about it would be answering for a resource it does not
host.

What is here is the arithmetic the protocol does on sets of them, in one place, because
"issue only what was consented to" is a subset check that is wrong in exactly one direction.
-/

@[expose] public section

namespace Authentication.OAuth

structure Scope where
  value : String
  deriving DecidableEq, Repr, Inhabited

namespace Scope

/-- Space delimited, as RFC 6749 §3.3 spells it. Duplicates collapse, so a request asking for
the same scope twice is the same request as one asking once. -/
def parse (raw : String) : List Scope :=
  ((raw.splitOn " ").filter (!·.isEmpty)).eraseDups.map fun value => ⟨value⟩

def render (scopes : List Scope) : String :=
  String.intercalate " " (scopes.map (·.value))

def subset (inner outer : List Scope) : Bool := inner.all (outer.contains ·)

/-- What a request is entitled to: those of the scopes it asked for that were consented to.
Filtering the request rather than intersecting the consent is what keeps the result ordered the
way the client asked and free of anything it did not. -/
def granted (requested consented : List Scope) : List Scope :=
  requested.filter (consented.contains ·)

/-- What an operation still needs, which is what a challenge names so the client can come back
for it (RFC 6750 §3.1). -/
def missing (required held : List Scope) : List Scope :=
  required.filter (!held.contains ·)

end Scope

end Authentication.OAuth
