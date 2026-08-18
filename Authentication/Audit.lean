/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Authentication.Response
import Authentication.Suppression
import Authentication.Tenant
import Authentication.Time

namespace Authentication

/-- Which side of the device boundary a magic link was opened on (AUTH-14.1.7). -/
inductive Device where
  | same
  | cross
  deriving DecidableEq, Repr, Inhabited

inductive CodeOutcome where
  | accepted
  | rejected
  | budgetExhausted
  deriving DecidableEq, Repr, Inhabited

inductive AbandonReason where
  | superseded
  | codeBudgetExhausted
  deriving DecidableEq, Repr, Inhabited

/-- Why sessions were revoked. AUTH-9.6 names three occasions on which all of an account's
sessions must go, and which one it was is the question asked of the log afterwards. -/
inductive RevocationReason where
  | requested
  | primaryEmailChanged
  | accountDeactivated
  | recovery
  deriving DecidableEq, Repr, Inhabited

/-- The true outcome is recorded whatever the person was told (AUTH-14.2.6), and a rejected
signup is recorded with its real reason (AUTH-7.7). -/
inductive AuditEvent (tenant : TenantId) where
  | attemptCreated (attempt : AttemptId tenant)
  | linkOpened (attempt : AttemptId tenant) (device : Device)
  | codeEntered (attempt : AttemptId tenant) (outcome : CodeOutcome)
  | attemptAbandoned (attempt : AttemptId tenant) (reason : AbandonReason)
  | sessionIssued (attempt : AttemptId tenant)
  | invitationConsumed (invitation : InvitationId tenant)
  | signInRejected (outcome : SignInOutcome)
  | sessionRevoked (session : SessionId tenant)
  | accountSessionsRevoked (account : AccountId tenant) (reason : RevocationReason)
  | primaryEmailChanged (account : AccountId tenant)
  | accountDeactivated (account : AccountId tenant)
  | accountReactivated (account : AccountId tenant)
  /-- The address is in the log because the log is where "why did this person stop receiving
  mail" is answered, and it is already the tenant's own data. -/
  | addressSuppressed (address : NormalisedEmail) (reason : SuppressionReason)
  | suppressionCleared (address : NormalisedEmail)
  deriving DecidableEq, Repr

/-- Append-only (AUTH-15.4.5). The actor is whatever the client said it was; the library
records that the client claimed it, not that the claim was true (AUTH-13.7). -/
structure AuditEntry (tenant : TenantId) where
  occurredAt : Timestamp
  actor : Actor
  event : AuditEvent tenant
  deriving DecidableEq, Repr

end Authentication
