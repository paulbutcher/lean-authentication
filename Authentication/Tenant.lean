/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public section

namespace Authentication

/--
A foreign key into the client's own notion of an organisation. The library holds nothing else
about a tenant (AUTH-4.1.3).
-/
structure TenantId where
  value : String
  deriving DecidableEq, Repr, Inhabited, Hashable

/-!
Every identifier below is indexed by the tenant it belongs to, so a query or a comparison that
crosses tenants does not typecheck (AUTH-4.2.4). This is the type-level guarantee AUTH-16.2
asks for in preference to a rule the caller has to remember.
-/

structure AccountId (tenant : TenantId) where
  value : String
  deriving DecidableEq, Repr

structure AttemptId (tenant : TenantId) where
  value : String
  deriving DecidableEq, Repr

structure SessionId (tenant : TenantId) where
  value : String
  deriving DecidableEq, Repr

structure InvitationId (tenant : TenantId) where
  value : String
  deriving DecidableEq, Repr

structure CredentialId (tenant : TenantId) where
  value : String
  deriving DecidableEq, Repr

/-- Who the client says performed an action. The library cannot verify it (AUTH-13.7). -/
inductive Actor where
  | anonymous
  | client (reference : String)
  deriving DecidableEq, Repr, Inhabited

end Authentication
