/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Authentication.Account
public import Authentication.Invitation
public import Authentication.Template

/-!
Who is being signed in, and by which of the two routes they got here.

This is its own module because it is the one type both routes share. The magic link state machine
constructs one variant and never the other, and a type whose variants include a federated sign-in
would be out of place in it.
-/

public section

namespace Authentication

/-- How the address below came to be proven. -/
inductive SessionOrigin (tenant : TenantId) where
  /-- The attempt that proved it, which is what the audit record of the sign-in names. -/
  | magicLink (attempt : AttemptId tenant)
  /-- A provider asserted it. `addressVerified` is the provider's own word for whether it has
  checked the address, and is the single fact AUTH-6.7 turns on. -/
  | federated (identity : FederatedIdentity) (addressVerified : Bool)
  deriving DecidableEq, Repr

structure SessionSubject (tenant : TenantId) where
  origin : SessionOrigin tenant
  address : EmailAddress
  invitation : Option (InvitationId tenant) := none
  /-- The browser the session is issued to. On the magic link route every completion path checks
  the binding nonce, so no other browser can reach this point; on the federated route it is the
  browser that came back with `state`. It is what a session listing shows the account holder
  about the session (AUTH-9.5). -/
  requester : RequestContext
  deriving DecidableEq, Repr

end Authentication
