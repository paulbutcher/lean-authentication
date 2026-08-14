/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Authentication.Digest
import Authentication.Email
import Authentication.Tenant
import Authentication.Time

namespace Authentication

inductive AccountStatus where
  | active
  | deactivated
  deriving DecidableEq, Repr, Inhabited

/-- Identified by the pair (tenant, normalised email). The same address in two tenants is two
accounts sharing nothing (AUTH-4.2.1). -/
structure Account (tenant : TenantId) where
  id : AccountId tenant
  identity : NormalisedEmail
  primaryEmail : EmailAddress
  additionalEmails : List NormalisedEmail := []
  status : AccountStatus := .active
  createdAt : Timestamp
  deriving DecidableEq, Repr

/-- Kinds are open by intent: a passkey or a second factor becomes another kind rather than
another column, so adding one is not a schema rewrite (AUTH-4.4.2). -/
inductive CredentialKind where
  | emailAddress
  | federatedIdentity
  deriving DecidableEq, Repr, Inhabited

/-- One means of proving identity. `descriptor` carries the kind's own key: the normalised
address for `emailAddress`, and issuer and subject for `federatedIdentity`, which is what an
external identity is keyed on rather than the address the provider asserts (AUTH-6.6). -/
structure Credential (tenant : TenantId) where
  id : CredentialId tenant
  account : AccountId tenant
  kind : CredentialKind
  descriptor : String
  digest : Option Digest := none
  createdAt : Timestamp
  deriving DecidableEq, Repr

/-- Server-side, so it can be revoked; a signed cookie carrying its own claims cannot be
(AUTH-9.1). -/
structure Session (tenant : TenantId) where
  id : SessionId tenant
  account : AccountId tenant
  identifierDigest : Digest
  createdAt : Timestamp
  lastSeenAt : Timestamp
  idleExpiresAt : Timestamp
  absoluteExpiresAt : Timestamp
  userAgent : Option String := none
  approximateLocation : Option String := none
  revokedAt : Option Timestamp := none
  deriving DecidableEq, Repr

/-- What validating a session yields: identity and tenant, and nothing else. Permission
resolution is entirely the client's (AUTH-9.7, AUTH-13.4). -/
structure SessionIdentity (tenant : TenantId) where
  account : AccountId tenant
  deriving DecidableEq, Repr

namespace Session

/-- Expiry is enforced on read, so correctness does not depend on a sweeper having run
(AUTH-15.4.3). -/
def identify {tenant : TenantId} (s : Session tenant) (now : Timestamp) :
    Option (SessionIdentity tenant) :=
  if s.revokedAt.isSome then none
  else if s.idleExpiresAt ≤ now then none
  else if s.absoluteExpiresAt ≤ now then none
  else some ⟨s.account⟩

end Session

end Authentication
