/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Authentication.Digest
public import Authentication.Email
public import Authentication.Error
public import Authentication.Tenant
public import Authentication.Time

public section

namespace Authentication

/-- Stored verbatim and returned on acceptance without being interpreted. This is how a client
attaches its own roles to an invitation while roles stay out of the library (AUTH-8.7,
AUTH-13.3). -/
structure InvitationMetadata where
  payload : String
  deriving DecidableEq, Repr, Inhabited

inductive InvitationState where
  | pending
  | accepted
  | revoked
  deriving DecidableEq, Repr, Inhabited

/-- A grant on one address in one tenant (AUTH-4.4.4). -/
structure Invitation (tenant : TenantId) where
  id : InvitationId tenant
  address : EmailAddress
  tokenDigest : Digest
  metadata : InvitationMetadata
  state : InvitationState := .pending
  expiresAt : Timestamp
  createdBy : Actor
  consumedAt : Option Timestamp := none
  deriving DecidableEq, Repr

/-- What acceptance authorises. Both the address and the tenant come from the invitation
record; neither can be supplied at accept time (AUTH-8.3). -/
structure InvitationGrant (tenant : TenantId) where
  invitation : InvitationId tenant
  address : EmailAddress
  metadata : InvitationMetadata
  deriving DecidableEq, Repr

namespace Invitation

/--
Says what an invitation grants, without spending it.

There is deliberately no address parameter. An accept form that submitted one would be the
whole vulnerability of AUTH-8.3, so the signature does not admit one.

Checking and spending are separate because they happen at different moments. The token is
presented when the link is opened, and the invitation is only spent once an account actually
exists, so an acceptance that is begun and abandoned does not burn it (AUTH-8.4, AUTH-8.5).
-/
def verify {tenant : TenantId} (now : Timestamp) (invitation : Invitation tenant)
    (presented : PresentedSecret) : Except AuthError (InvitationGrant tenant) :=
  if invitation.state != .pending then .error .invitationNotPending
  else if invitation.expiresAt ≤ now then .error .invitationExpired
  else if !invitation.tokenDigest.accepts presented then .error .unknownToken
  else
    .ok
      { invitation := invitation.id
        address := invitation.address
        metadata := invitation.metadata }

/-- What spending one leaves behind. Written under compare-and-set, so two requests racing to
accept one invitation produce one account (AUTH-8.5). -/
def markConsumed {tenant : TenantId} (now : Timestamp) (invitation : Invitation tenant) :
    Invitation tenant :=
  { invitation with state := .accepted, consumedAt := some now }

/-- Single use: acceptance moves the invitation to `accepted`, and a second attempt finds it no
longer pending (AUTH-8.5). -/
def consume {tenant : TenantId} (now : Timestamp) (invitation : Invitation tenant)
    (presented : PresentedSecret) :
    Except AuthError (Invitation tenant × InvitationGrant tenant) :=
  (verify now invitation presented).map fun grant => (markConsumed now invitation, grant)

end Invitation

end Authentication
