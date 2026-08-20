/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Authentication.Account
import Authentication.Attempt
import Authentication.Audit
import Authentication.Consent
import Authentication.Invitation
import Authentication.Suppression

/-!
The storage port (AUTH-15.2).

The public seam is a domain-level repository: it speaks accounts, attempts, sessions and
invitations, never SQL and never a connection. A backend that is not a relational database has
to be implementable against it.

Its contract is not its type signature. The guarantees in AUTH-15.4 are the part a backend can
typecheck while violating, which is why they are written out on the operations below and
checked by `Authentication.Store.Conformance`.
-/

namespace Authentication

inductive StoreError where
  | duplicateAccount
  | duplicateCredential
  | unknownAccount
  deriving DecidableEq, Repr, Inhabited

/-- Account creation reports whether the new account is the first in its tenant, because with
no roles in the library nothing else can make a tenant's first account privileged, and every
client would otherwise discover this when its first tenant turns out to have no administrator
(AUTH-13.6). -/
structure AccountCreated (tenant : TenantId) where
  account : Account tenant
  firstInTenant : Bool
  deriving Repr

/-- What a sweep removed (AUTH-15.4.3). -/
structure PurgeCounts where
  attempts : Nat := 0
  sessions : Nat := 0
  deriving DecidableEq, Repr, Inhabited

/--
Every operation takes the tenant, and every identifier it accepts carries the tenant in its
type, so a query that reads another tenant's rows cannot be written (AUTH-4.2.4).
-/
structure AuthStore (m : Type → Type) where
  /-- `none` when no account in this tenant has that identity. The same address in another
  tenant is a different account and is not visible here (AUTH-4.2.1). -/
  accountByIdentity : (tenant : TenantId) → NormalisedEmail → m (Option (Account tenant))
  /-- Uniqueness on (tenant, identity) is enforced here rather than checked by the caller: a
  caller that looks first and inserts second has a race, and the race creates the duplicate
  account (AUTH-15.4.2). -/
  createAccount : (tenant : TenantId) → Account tenant → m (Except StoreError (AccountCreated tenant))
  accountById : (tenant : TenantId) → AccountId tenant → m (Option (Account tenant))
  /-- Changing the address an account is identified by, which is the same uniqueness question
  creation asks and gets the same answer from the store rather than from the caller
  (AUTH-15.4.2). -/
  setPrimaryEmail : (tenant : TenantId) → AccountId tenant → EmailAddress →
    m (Except StoreError Unit)
  /-- Deactivation is a stored state rather than a deletion, because an account nobody can sign
  in to still owns the audit record of everything it did. -/
  setAccountStatus : (tenant : TenantId) → AccountId tenant → AccountStatus →
    m (Except StoreError Unit)
  /-- Inserts the attempt and abandons any attempt already live for the same address in one
  step, returning what it abandoned so the caller can record it. Doing this in two calls would
  leave a window in which two attempts are live, and an attacker who can farm concurrent
  attempts multiplies the code guess budget (AUTH-5.2.9). -/
  startAttempt : (tenant : TenantId) → AttemptState tenant → m (List (AttemptId tenant))
  attemptById : (tenant : TenantId) → AttemptId tenant → m (Option (AttemptState tenant))
  /-- Compare and set, never read then write. Writes `next` only if the stored attempt still
  agrees with `expected` about its phase and its failed-entry count, and reports whether it
  won. Two concurrent completions of one attempt therefore produce exactly one session
  (AUTH-5.3.5, AUTH-15.4.1). -/
  commitAttempt : (tenant : TenantId) → (expected next : AttemptState tenant) → m Bool
  createSession : (tenant : TenantId) → Session tenant → m Unit
  /-- Expiry and revocation are enforced here, so correctness does not depend on a sweeper
  having run (AUTH-15.4.3). A read that follows a write observes it: a just-issued session
  failing its first validation is indistinguishable from a broken sign-in (AUTH-15.4.6). -/
  sessionByDigest : (tenant : TenantId) → Timestamp → Digest → m (Option (Session tenant))
  sessionsForAccount : (tenant : TenantId) → Timestamp → AccountId tenant → m (List (Session tenant))
  /-- Slides the idle timeout of AUTH-9.4 and records that the session was used. It is given the
  new expiry rather than the timeout, so the ceiling of the absolute lifetime is applied once,
  where the session is known, instead of by every backend. -/
  touchSession : (tenant : TenantId) → SessionId tenant → (lastSeenAt idleExpiresAt : Timestamp) →
    m Unit
  revokeSession : (tenant : TenantId) → Timestamp → SessionId tenant → m Unit
  /-- Used on primary email change, deactivation, and any recovery action (AUTH-9.6). -/
  revokeSessionsForAccount : (tenant : TenantId) → Timestamp → AccountId tenant → m Unit
  createInvitation : (tenant : TenantId) → Invitation tenant → m Unit
  invitationById : (tenant : TenantId) → InvitationId tenant → m (Option (Invitation tenant))
  /-- Compare and set on the invitation's state, so an invitation is single use however many
  requests race to accept it (AUTH-8.5). It writes the token digest and expiry too, which is
  what lets a resend rotate the token and invalidate the old one in the same operation. -/
  commitInvitation : (tenant : TenantId) → (expected next : Invitation tenant) → m Bool
  invitationsForTenant : (tenant : TenantId) → m (List (Invitation tenant))
  /-- Counts one failure against the address and returns what the history now says. It is one
  operation rather than a read and a write because two bounces arriving together would otherwise
  count as one, and the count is what AUTH-12.5 reports on. -/
  recordDeliveryFailure : (tenant : TenantId) → NormalisedEmail → DeliveryFailure → Timestamp →
    (detail : String) → m (DeliveryRecord tenant)
  /-- Suppression by the client, for an address it knows about from somewhere this library
  cannot see (AUTH-12.1). -/
  suppressAddress : (tenant : TenantId) → NormalisedEmail → Timestamp → (detail : String) →
    m (DeliveryRecord tenant)
  deliveryRecord : (tenant : TenantId) → NormalisedEmail → m (Option (DeliveryRecord tenant))
  deliveryRecords : (tenant : TenantId) → m (List (DeliveryRecord tenant))
  /-- Addresses get fixed, so suppression has to be liftable (AUTH-12.4). It removes the history
  as well as the suppression: an address that has been repaired starts from no failures, or the
  count that reported it stays high for ever. -/
  clearSuppression : (tenant : TenantId) → NormalisedEmail → m Unit
  /-- Append only, for the reason the audit log is: a withdrawal is another entry rather than an
  edit to the entry that granted, so what the record says was agreed to at the time cannot be
  changed afterwards (AUTH-4.6.3). -/
  recordConsent : (tenant : TenantId) → ConsentEntry tenant → m Unit
  /-- Oldest first, so the last entry about a subject is the current answer (AUTH-4.6.4). -/
  consentHistory : (tenant : TenantId) → AccountId tenant → m (List (ConsentEntry tenant))
  /-- The accounts whose last word on this subject was a grant, which is the query a mailshot
  is drawn from (AUTH-4.6.5). It is an operation rather than a fold the client writes over
  every account's history, because that fold is the part that gets written wrong, and wrongly
  in the direction of mailing somebody who said no. -/
  consentingAccounts : (tenant : TenantId) → ConsentSubject → m (List (AccountId tenant))
  /-- Append only. The port offers no update and no delete, which is how AUTH-15.4.5 is kept:
  not by a rule a backend is asked to follow but by an operation it is not given. -/
  appendAudit : (tenant : TenantId) → AuditEntry tenant → m Unit
  auditEntries : (tenant : TenantId) → m (List (AuditEntry tenant))
  /-- Removes attempts that expired before `before`, and sessions that can no longer be used and
  stopped being usable before it. Everything it removes is already refused on read, so no
  correctness depends on it having run; what it bounds is growth (AUTH-15.4.3).

  It sweeps nothing else. The audit log, consent records and delivery history are retention
  questions rather than expiry ones, and the port offers no way to remove one of those. -/
  purgeExpired : (tenant : TenantId) → (before : Timestamp) → m PurgeCounts
  /-- Removes the tenant's accounts, sessions, invitations, attempts, delivery history, consent
  records and audit records, with no orphans (AUTH-4.2.5). -/
  deleteTenant : (tenant : TenantId) → m Unit

/--
Enlisting in the client's transaction is a separate capability, not part of the base port
(AUTH-15.3.1). A backend supplying only `AuthStore` is valid and serves clients that do not
need atomic provisioning; a client that does need it asks for this type, and a backend without
it fails to compile rather than failing at runtime (AUTH-15.3.3).

`runInTx` is a scoped block rather than an exposed handle, so a backend that is not a
relational database can implement it (AUTH-15.3.4).

The price, which the documentation has to state plainly: enlistment requires the library's
tables to live in the client's own database, so a client using it cannot put authentication
data elsewhere (AUTH-15.3.5).
-/
structure TransactionalStore (m : Type → Type) where
  store : AuthStore m
  runInTx : {α : Type} → (AuthStore m → m α) → m α

end Authentication
