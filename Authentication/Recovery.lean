/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Authentication.Digest
public import Authentication.Error
public import Authentication.Tenant
public import Authentication.Time

public section

namespace Authentication

/-- What enrolling under a grant does to the credentials the account already holds. The default
is to remove them, because the usual reason for recovery is that a device is gone and a passkey
on it should not keep working; a client that knows otherwise says so (AUTH-9.10.5). -/
inductive RecoveryDisposition where
  | removeExisting
  | keepExisting
  deriving DecidableEq, Repr, Inhabited

inductive RecoveryGrantState where
  | pending
  | spent
  | revoked
  deriving DecidableEq, Repr, Inhabited

/--
An administrator's statement that one account may enrol one credential without holding a session
(AUTH-9.10).

It authorises an enrolment and never a sign-in, which is what keeps it inside the origin policy
rather than an exception to it: AUTH-9.9.5 already has it that adding a credential issues no
session, so the sign-in that follows is checked like any other.
-/
structure RecoveryGrant (tenant : TenantId) where
  id : RecoveryGrantId tenant
  account : AccountId tenant
  tokenDigest : Digest
  disposition : RecoveryDisposition := .removeExisting
  state : RecoveryGrantState := .pending
  expiresAt : Timestamp
  createdBy : Actor
  spentAt : Option Timestamp := none
  deriving DecidableEq, Repr

/-- What redeeming one authorises. The account comes from the record and there is no parameter
for one, which is what makes AUTH-9.10.3 unbreakable here rather than merely unbroken: a
redemption that named an account would enrol whoever asked onto whichever account they named. -/
structure RecoveryAuthorisation (tenant : TenantId) where
  grant : RecoveryGrantId tenant
  account : AccountId tenant
  disposition : RecoveryDisposition
  deriving DecidableEq, Repr

namespace RecoveryGrant

/--
Says what a grant authorises, without spending it.

Checking and spending are separate for the reason they are separate on an invitation, and the
reason bites harder here. The token is presented when the ceremony begins and the grant is spent
only once a credential exists, so a ceremony that is begun and abandoned does not burn it. The
person holding one has just lost the credential they used to sign in with, and is meeting an
authenticator dialog that refuses for several ordinary reasons.
-/
def verify {tenant : TenantId} (now : Timestamp) (grant : RecoveryGrant tenant)
    (presented : PresentedSecret) : Except AuthError (RecoveryAuthorisation tenant) :=
  if grant.state != .pending then .error .recoveryNotPending
  else if grant.expiresAt ≤ now then .error .recoveryExpired
  else if !grant.tokenDigest.accepts presented then .error .unknownToken
  else
    .ok
      { grant := grant.id
        account := grant.account
        disposition := grant.disposition }

/-- What spending one leaves behind. Written under compare-and-set, so two ceremonies racing to
redeem one grant enrol one credential (AUTH-9.10.4). -/
def markSpent {tenant : TenantId} (now : Timestamp) (grant : RecoveryGrant tenant) :
    RecoveryGrant tenant :=
  { grant with state := .spent, spentAt := some now }

end RecoveryGrant

end Authentication
