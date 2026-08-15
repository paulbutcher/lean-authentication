/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Authentication.Store

/-!
The conformance suite (AUTH-15.5).

Every guarantee in AUTH-15.4 is something a backend can typecheck while violating, so pluggable
storage without this would mean each new backend is an unreviewed reimplementation of the
security-critical parts. The suite ships with the library and is meant to be run by third
parties against their own backends, which is why it lives here and not in the test directory.

Each run uses tenant identifiers derived from `label`, so the suite can be pointed at a real
database and run repeatedly without colliding with itself.
-/

namespace Authentication.Store.Conformance

structure Check where
  name : String
  passed : Bool
  deriving Repr, DecidableEq, Inhabited

private def key : KeyId := ⟨"conformance"⟩

private def digestOf (bytes : List UInt8) : Digest := ⟨key, bytes⟩

private def addressOf (localPart : String) : EmailAddress := ⟨localPart, ⟨["example", "com"]⟩⟩

private def epoch : Timestamp := ⟨1700000000⟩
private def soon : Timestamp := ⟨1700000600⟩
private def later : Timestamp := ⟨1700007200⟩

private def sampleAttempt (tenant : TenantId) (id : String) (address : EmailAddress)
    (expiresAt : Timestamp) : AttemptState tenant :=
  { id := ⟨id⟩
    address
    phase := .pending
    magicToken := digestOf [1, 1]
    revealedCode := digestOf [2, 2]
    emailedCode := none
    bindingNonce := digestOf [3, 3]
    failedCodeEntries := 0
    expiresAt
    requester := {} }

private def sampleAccount (tenant : TenantId) (id : String) (address : EmailAddress) :
    Account tenant :=
  { id := ⟨id⟩
    identity := address.normalise
    primaryEmail := address
    createdAt := epoch }

private def sampleSession (tenant : TenantId) (id : String) (account : AccountId tenant)
    (identifierDigest : Digest) (idleExpiresAt absoluteExpiresAt : Timestamp) : Session tenant :=
  { id := ⟨id⟩
    account
    identifierDigest
    createdAt := epoch
    lastSeenAt := epoch
    idleExpiresAt
    absoluteExpiresAt }

private def sampleInvitation (tenant : TenantId) (id : String) (address : EmailAddress) :
    Invitation tenant :=
  { id := ⟨id⟩
    address
    tokenDigest := digestOf [4, 4]
    metadata := ⟨"{\"role\":\"member\"}"⟩
    expiresAt := later
    createdBy := .client "conformance" }

/--
Runs every check against `store`.

The concurrent cases of AUTH-15.5.1 are exercised by interleaving deterministically: two
callers read the same record, then both write. That is the situation compare-and-set exists to
survive, and running it deterministically means a backend that fails does so every time rather
than on the run nobody was watching.
-/
def run {m : Type → Type} [Monad m] (store : AuthStore m) (label : String := "conformance") :
    m (List Check) := do
  let alpha : TenantId := ⟨label ++ "-alpha"⟩
  let beta : TenantId := ⟨label ++ "-beta"⟩
  let doomed : TenantId := ⟨label ++ "-doomed"⟩
  let person := addressOf "person"
  let other := addressOf "other"

  -- A backend that persists has to start from the same place as one that does not, or the suite
  -- passes once and then reports uniqueness failures that are its own leftovers.
  store.deleteTenant alpha
  store.deleteTenant beta
  store.deleteTenant doomed

  -- Accounts, uniqueness, and the first-account signal.
  let created ← store.createAccount alpha (sampleAccount alpha "account-1" person)
  let firstReported :=
    match created with
    | .ok result => result.firstInTenant
    | .error _ => false
  let readBack ← store.accountByIdentity alpha person.normalise
  let duplicate ← store.createAccount alpha (sampleAccount alpha "account-2" person)
  let secondCreated ← store.createAccount alpha (sampleAccount alpha "account-3" other)
  let secondReported :=
    match secondCreated with
    | .ok result => result.firstInTenant
    | .error _ => true
  let crossTenantAccount ← store.accountByIdentity beta person.normalise

  -- Attempts: at most one live per address, and compare-and-set on commit.
  let first := sampleAttempt alpha "attempt-1" person soon
  let _ ← store.startAttempt alpha first
  let superseded ← store.startAttempt alpha (sampleAttempt alpha "attempt-2" person soon)
  let firstAfterSupersede ← store.attemptById alpha first.id
  let live := sampleAttempt alpha "attempt-3" other soon
  let _ ← store.startAttempt alpha live
  let readerOne ← store.attemptById alpha live.id
  let readerTwo ← store.attemptById alpha live.id
  let commits ←
    match readerOne, readerTwo with
    | some one, some two => do
      let wonFirst ← store.commitAttempt alpha one { one with phase := .completed }
      let wonSecond ← store.commitAttempt alpha two { two with phase := .abandoned }
      pure (some (wonFirst, wonSecond))
    | _, _ => pure none
  let afterCommit ← store.attemptById alpha live.id
  let crossTenantAttempt ← store.attemptById beta ⟨"attempt-3"⟩

  -- Sessions: found by digest, and gone once expired, revoked, or past their absolute life.
  let account : AccountId alpha := ⟨"account-1"⟩
  let liveDigest := digestOf [10]
  let idleDigest := digestOf [11]
  let staleDigest := digestOf [12]
  let revokedDigest := digestOf [13]
  store.createSession alpha (sampleSession alpha "session-live" account liveDigest later later)
  store.createSession alpha (sampleSession alpha "session-idle" account idleDigest epoch later)
  store.createSession alpha (sampleSession alpha "session-stale" account staleDigest later epoch)
  store.createSession alpha
    (sampleSession alpha "session-revoked" account revokedDigest later later)
  let foundLive ← store.sessionByDigest alpha soon liveDigest
  let foundIdle ← store.sessionByDigest alpha soon idleDigest
  let foundStale ← store.sessionByDigest alpha soon staleDigest
  store.revokeSession alpha soon ⟨"session-revoked"⟩
  let foundRevoked ← store.sessionByDigest alpha soon revokedDigest
  let crossTenantSession ← store.sessionByDigest beta soon liveDigest
  let ownSessions ← store.sessionsForAccount alpha soon account
  store.revokeSessionsForAccount alpha soon account
  let afterMassRevoke ← store.sessionsForAccount alpha soon account

  -- Invitations are single use however many requests race to accept.
  let invitation := sampleInvitation alpha "invitation-1" other
  store.createInvitation alpha invitation
  let invitationReaderOne ← store.invitationById alpha invitation.id
  let invitationReaderTwo ← store.invitationById alpha invitation.id
  let invitationCommits ←
    match invitationReaderOne, invitationReaderTwo with
    | some one, some two => do
      let wonFirst ← store.commitInvitation alpha one
        { one with state := .accepted, consumedAt := some soon }
      let wonSecond ← store.commitInvitation alpha two
        { two with state := .accepted, consumedAt := some soon }
      pure (some (wonFirst, wonSecond))
    | _, _ => pure none

  -- The audit log, and that it stays inside its tenant.
  store.appendAudit alpha ⟨soon, .anonymous, .attemptCreated ⟨"attempt-3"⟩⟩
  store.appendAudit beta ⟨soon, .anonymous, .attemptCreated ⟨"attempt-elsewhere"⟩⟩
  let alphaAudit ← store.auditEntries alpha
  let betaAudit ← store.auditEntries beta

  -- Tenant deletion cascades, and stops at the tenant it was asked about.
  let _ ← store.createAccount doomed (sampleAccount doomed "account-doomed" person)
  let _ ← store.startAttempt doomed (sampleAttempt doomed "attempt-doomed" person soon)
  store.createSession doomed
    (sampleSession doomed "session-doomed" ⟨"account-doomed"⟩ (digestOf [20]) later later)
  store.createInvitation doomed (sampleInvitation doomed "invitation-doomed" person)
  store.appendAudit doomed ⟨soon, .anonymous, .attemptCreated ⟨"attempt-doomed"⟩⟩
  store.deleteTenant doomed
  let doomedAccount ← store.accountByIdentity doomed person.normalise
  let doomedAttempt ← store.attemptById doomed ⟨"attempt-doomed"⟩
  let doomedSession ← store.sessionByDigest doomed soon (digestOf [20])
  let doomedInvitation ← store.invitationById doomed ⟨"invitation-doomed"⟩
  let doomedAudit ← store.auditEntries doomed
  let survivingAccount ← store.accountByIdentity alpha person.normalise

  pure
    [ { name := "an account is readable by the identity it was created with"
        passed := (readBack.map (·.id.value)) == some "account-1" }
    , { name := "the first account in a tenant is reported as the first (AUTH-13.6)"
        passed := firstReported }
    , { name := "a later account is not reported as the first"
        passed := !secondReported }
    , { name := "a second account with the same identity is refused (AUTH-15.4.2)"
        passed := duplicate matches .error _ }
    , { name := "an account is invisible from another tenant (AUTH-15.4.4)"
        passed := crossTenantAccount.isNone }
    , { name := "starting an attempt reports the one it superseded (AUTH-5.2.9)"
        passed := superseded.map (·.value) == [first.id.value] }
    , { name := "the superseded attempt is left abandoned"
        passed := (firstAfterSupersede.map (·.phase)) == some .abandoned }
    , { name := "the first of two concurrent commits wins (AUTH-15.4.1)"
        passed := commits == some (true, false) }
    , { name := "the losing commit left no trace"
        passed := (afterCommit.map (·.phase)) == some .completed }
    , { name := "an attempt is invisible from another tenant"
        passed := crossTenantAttempt.isNone }
    , { name := "a live session is found by its digest (AUTH-15.4.6)"
        passed := (foundLive.map (·.id.value)) == some "session-live" }
    , { name := "a session past its idle timeout is not returned (AUTH-15.4.3)"
        passed := foundIdle.isNone }
    , { name := "a session past its absolute lifetime is not returned"
        passed := foundStale.isNone }
    , { name := "a revoked session is not returned"
        passed := foundRevoked.isNone }
    , { name := "a session is invisible from another tenant"
        passed := crossTenantSession.isNone }
    , { name := "an account's live sessions are listed"
        passed := ownSessions.length == 1 }
    , { name := "revoking an account's sessions revokes all of them (AUTH-9.6)"
        passed := afterMassRevoke.isEmpty }
    , { name := "an invitation can be accepted only once (AUTH-8.5)"
        passed := invitationCommits == some (true, false) }
    , { name := "audit entries are readable in the tenant they were written for"
        passed := alphaAudit.length == 1 }
    , { name := "audit entries do not leak across tenants"
        passed := betaAudit.length == 1 }
    , { name := "deleting a tenant removes its accounts (AUTH-4.2.5)"
        passed := doomedAccount.isNone }
    , { name := "deleting a tenant removes its attempts"
        passed := doomedAttempt.isNone }
    , { name := "deleting a tenant removes its sessions"
        passed := doomedSession.isNone }
    , { name := "deleting a tenant removes its invitations"
        passed := doomedInvitation.isNone }
    , { name := "deleting a tenant removes its audit records"
        passed := doomedAudit.isEmpty }
    , { name := "deleting a tenant leaves other tenants alone"
        passed := survivingAccount.isSome } ]

end Authentication.Store.Conformance
