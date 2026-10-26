/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Authentication.Store

/-!
The conformance suite (AUTH-15.5).

Every guarantee in AUTH-15.4 is something a backend can typecheck while violating, so pluggable
storage without this would mean each new backend is an unreviewed reimplementation of the
security-critical parts. The suite ships with the library and is meant to be run by third
parties against their own backends, which is why it lives here and not in the test directory.

Each run uses tenant identifiers derived from `label`, so the suite can be pointed at a real
database and run repeatedly without colliding with itself.
-/

public section

namespace Authentication.Store.Conformance

structure Check where
  name : String
  passed : Bool
  deriving Repr, DecidableEq, Inhabited

private def key : KeyId := ⟨"conformance"⟩

private def digestOf (bytes : List UInt8) : Digest := ⟨key, ⟨bytes.toArray⟩⟩

private def addressOf (localPart : String) : EmailAddress := ⟨localPart, ⟨["example", "com"]⟩⟩

/--
One of each event an audit entry can carry: every case of `AuditEvent`, each once for every value
of the enumeration it carries. A backend that maps an event in one direction only drops the entry
without a word, and the last such mistake was in an enumeration rather than a case, so the round
trip has to cover both. `Tests.AuditCoverage` proves that nothing is missing.
-/
@[expose] def everyAuditEvent (tenant : TenantId) : List (AuditEvent tenant) :=
  let attempt : AttemptId tenant := ⟨"attempt-1"⟩
  let account : AccountId tenant := ⟨"account-1"⟩
  let address := (⟨"logged", ⟨["example", "com"]⟩⟩ : EmailAddress).normalise
  [.attemptCreated attempt]
    ++ [Device.same, .cross].map (.linkOpened attempt)
    ++ [CodeOutcome.accepted, .rejected, .budgetExhausted].map (.codeEntered attempt)
    ++ [AbandonReason.superseded, .codeBudgetExhausted].map (.attemptAbandoned attempt)
    ++ [.sessionIssued attempt, .invitationConsumed ⟨"invitation-1"⟩]
    ++ [SignInOutcome.linkSent, .notInvited, .domainNotAllowed, .addressSuppressed,
        .accountDeactivated, .addressNotVerified, .originNotPermitted, .throttled,
        .malformedAddress].map .signInRejected
    ++ [.sessionRevoked ⟨"session-1"⟩]
    ++ [RevocationReason.requested, .primaryEmailChanged, .accountDeactivated, .recovery].map
        (.accountSessionsRevoked account)
    ++ [.primaryEmailChanged account, .accountDeactivated account, .accountReactivated account]
    ++ [SuppressionReason.hardBounce, .spamComplaint, .client].map (.addressSuppressed address)
    ++ [.suppressionCleared address, .consentGranted account ⟨"marketing"⟩,
        .consentWithdrawn account ⟨"marketing"⟩, .identityLinked account "https://issuer.test",
        .identityUnlinked account "https://issuer.test", .passkeyCounterRegressed account 7,
        .recoveryIssued account ⟨"grant-1"⟩, .recoveryRedeemed account ⟨"grant-1"⟩]

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

/-- Which refusal a session read reported, if it refused. `Session` is comparable and
`Except` is not, so the assertions below read the error side rather than the whole answer. -/
private def refusalOf {tenant : TenantId} (result : Except SessionRejection (Session tenant)) :
    Option SessionRejection :=
  match result with
  | .error reason => some reason
  | .ok _ => none

private def sampleInvitation (tenant : TenantId) (id : String) (address : EmailAddress) :
    Invitation tenant :=
  { id := ⟨id⟩
    address
    tokenDigest := digestOf [4, 4]
    metadata := ⟨"{\"role\":\"member\"}"⟩
    expiresAt := later
    createdBy := .client "conformance" }

private def sampleRecoveryGrant (tenant : TenantId) (id : String) (account : AccountId tenant) :
    RecoveryGrant tenant :=
  { id := ⟨id⟩
    account
    tokenDigest := digestOf [4, 5]
    expiresAt := later
    createdBy := .client "conformance" }

/-- A refusal, and the one it was supposed to be. `Except` has no `BEq` to compare against, and
naming the error is the point: a store that refuses for its own reasons still fails the check. -/
private def refused (expected : StoreError) : Except StoreError Unit → Bool
  | .error actual => actual == expected
  | .ok _ => false

private def sampleIdentity : FederatedIdentity := ⟨"https://issuer.example", "subject-1"⟩

private def sampleCredential (tenant : TenantId) (id : String) (account : AccountId tenant)
    (identity : FederatedIdentity) : Credential tenant :=
  { id := ⟨id⟩
    account
    descriptor := .federatedIdentity identity
    createdAt := epoch }

private def samplePasskeyCredential (tenant : TenantId) (id : String) (account : AccountId tenant)
    (passkey : PasskeyId) : Credential tenant :=
  { id := ⟨id⟩
    account
    descriptor := .passkey passkey
    createdAt := epoch }

private def samplePasskey (tenant : TenantId) (credential : String) (label : String)
    (signCount : UInt32 := 0) : PasskeyRegistration tenant :=
  { credential := ⟨credential⟩
    publicKey := ⟨#[4, 1, 2, 3]⟩
    algorithm := ⟨-7⟩
    signCount
    transports := ["internal", "hybrid"]
    aaguid := ⟨#[9, 9]⟩
    backupEligible := true
    backupState := false
    label
    createdAt := epoch }

private def samplePasskeyCeremony (tenant : TenantId) (id : String) (challenge : Digest)
    (expiresAt : Timestamp) : PasskeyCeremony tenant :=
  { id := ⟨id⟩
    kind := .authentication
    challenge
    bindingNonce := digestOf [5, 5]
    account := some ⟨"account-" ++ id⟩
    returnTo := some "/after"
    createdAt := epoch
    expiresAt }

private def sampleState (tenant : TenantId) (id : String) (digest : Digest)
    (expiresAt : Timestamp) : FederationState tenant :=
  { id := ⟨id⟩
    provider := ⟨"conformance"⟩
    stateDigest := digest
    verifier := "verifier-" ++ id
    nonce := "nonce-" ++ id
    returnTo := some "/after"
    invitation := some ⟨"invitation-" ++ id⟩
    account := some ⟨"account-" ++ id⟩
    createdAt := epoch
    expiresAt }

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
  let swept : TenantId := ⟨label ++ "-swept"⟩
  -- A tenant of its own for the audit round trip, so the check does not depend on running after
  -- whichever other tenant's entries were counted.
  let logged : TenantId := ⟨label ++ "-logged"⟩
  let person := addressOf "person"
  let other := addressOf "other"

  -- A backend that persists has to start from the same place as one that does not, or the suite
  -- passes once and then reports uniqueness failures that are its own leftovers.
  store.deleteTenant alpha
  store.deleteTenant beta
  store.deleteTenant doomed
  store.deleteTenant swept
  store.deleteTenant logged

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
  let byId ← store.accountById alpha ⟨"account-1"⟩
  let crossTenantById ← store.accountById beta ⟨"account-1"⟩

  -- Changing the identifying address, and the uniqueness that still applies to it.
  let moved := addressOf "moved"
  let renamed ← store.setPrimaryEmail alpha ⟨"account-1"⟩ moved
  let underNewAddress ← store.accountByIdentity alpha moved.normalise
  let underOldAddress ← store.accountByIdentity alpha person.normalise
  let collided ← store.setPrimaryEmail alpha ⟨"account-3"⟩ moved
  let missing ← store.setPrimaryEmail alpha ⟨"account-absent"⟩ (addressOf "nobody")
  let restored ← store.setPrimaryEmail alpha ⟨"account-1"⟩ person

  -- Deactivation is a state, not a deletion.
  let deactivated ← store.setAccountStatus alpha ⟨"account-3"⟩ .deactivated
  let afterDeactivation ← store.accountById alpha ⟨"account-3"⟩
  let statusOfMissing ← store.setAccountStatus alpha ⟨"account-absent"⟩ .deactivated
  let _ ← store.setAccountStatus alpha ⟨"account-3"⟩ .active

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

  -- Sessions: found by digest, and refused with the reason once expired, revoked, or past their
  -- absolute life.
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
  -- Touching slides the idle timeout (AUTH-9.4): this one is past its idle expiry at `soon` and
  -- live again once touched. The one already past its absolute lifetime is touched with the
  -- same later expiry, which a backend must not honour: the absolute lifetime is a ceiling.
  let touchDigest := digestOf [14]
  store.createSession alpha (sampleSession alpha "session-touch" account touchDigest soon later)
  let beforeTouch ← store.sessionByDigest alpha soon touchDigest
  store.touchSession alpha ⟨"session-touch"⟩ epoch later
  let afterTouch ← store.sessionByDigest alpha soon touchDigest
  store.touchSession alpha ⟨"session-stale"⟩ soon later
  let touchedStale ← store.sessionByDigest alpha soon staleDigest
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

  -- Delivery history: transient failures counted, permanent ones suppressing, and neither
  -- visible from another tenant (AUTH-12.2).
  let bouncing := addressOf "bouncing"
  let flaky := addressOf "flaky"
  let softOnce ← store.recordDeliveryFailure alpha flaky.normalise .softBounce epoch "full"
  let softTwice ← store.recordDeliveryFailure alpha flaky.normalise .softBounce soon "full"
  let hard ← store.recordDeliveryFailure alpha bouncing.normalise .hardBounce epoch "no such user"
  let softAfterHard ←
    store.recordDeliveryFailure alpha bouncing.normalise .softBounce soon "full"
  let crossTenantRecord ← store.deliveryRecord beta bouncing.normalise
  let allRecords ← store.deliveryRecords alpha
  store.clearSuppression alpha bouncing.normalise
  let afterClearing ← store.deliveryRecord alpha bouncing.normalise
  let byClient ← store.suppressAddress alpha flaky.normalise later "asked us to stop"

  -- Consent: append only, oldest first, and the last word deciding who is still consenting.
  let marketing : ConsentSubject := ⟨"marketing"⟩
  let terms : ConsentSubject := ⟨"terms"⟩
  store.recordConsent alpha ⟨⟨"account-1"⟩, terms, "2026-01", .granted, epoch⟩
  store.recordConsent alpha ⟨⟨"account-1"⟩, marketing, "2026-01", .granted, epoch⟩
  store.recordConsent alpha ⟨⟨"account-1"⟩, marketing, "2026-01", .withdrawn, soon⟩
  store.recordConsent alpha ⟨⟨"account-3"⟩, marketing, "2026-02", .granted, soon⟩
  store.recordConsent beta ⟨⟨"account-1"⟩, marketing, "2026-01", .granted, epoch⟩
  let consentTrail ← store.consentHistory alpha ⟨"account-1"⟩
  let crossTenantConsent ← store.consentHistory beta ⟨"account-3"⟩
  let stillConsenting ← store.consentingAccounts alpha marketing
  let consentingElsewhere ← store.consentingAccounts beta marketing

  -- The audit log, and that it stays inside its tenant.
  store.appendAudit alpha ⟨soon, .anonymous, .attemptCreated ⟨"attempt-3"⟩⟩
  store.appendAudit beta ⟨soon, .anonymous, .attemptCreated ⟨"attempt-elsewhere"⟩⟩
  let alphaAudit ← store.auditEntries alpha
  let betaAudit ← store.auditEntries beta

  -- Sweeping removes what nothing can reach, and leaves everything else.
  let _ ← store.createAccount swept (sampleAccount swept "account-swept" person)
  let _ ← store.startAttempt swept (sampleAttempt swept "attempt-live" other later)
  let _ ← store.startAttempt swept (sampleAttempt swept "attempt-stale" person epoch)
  store.createSession swept
    (sampleSession swept "session-live" ⟨"account-swept"⟩ (digestOf [30]) later later)
  store.createSession swept
    (sampleSession swept "session-idle" ⟨"account-swept"⟩ (digestOf [31]) epoch later)
  store.createSession swept
    (sampleSession swept "session-revoked" ⟨"account-swept"⟩ (digestOf [32]) later later)
  store.revokeSession swept epoch ⟨"session-revoked"⟩
  store.appendAudit swept ⟨epoch, .anonymous, .attemptCreated ⟨"attempt-stale"⟩⟩
  store.recordConsent swept ⟨⟨"account-swept"⟩, terms, "2026-01", .granted, epoch⟩
  let purged ← store.purgeExpired swept soon
  let sweptLiveAttempt ← store.attemptById swept ⟨"attempt-live"⟩
  let sweptStaleAttempt ← store.attemptById swept ⟨"attempt-stale"⟩
  let sweptLiveSession ← store.sessionByDigest swept soon (digestOf [30])
  let sweptAudit ← store.auditEntries swept
  let sweptConsent ← store.consentHistory swept ⟨"account-swept"⟩

  -- Tenant deletion cascades, and stops at the tenant it was asked about.
  let _ ← store.createAccount doomed (sampleAccount doomed "account-doomed" person)
  let _ ← store.startAttempt doomed (sampleAttempt doomed "attempt-doomed" person soon)
  store.createSession doomed
    (sampleSession doomed "session-doomed" ⟨"account-doomed"⟩ (digestOf [20]) later later)
  store.createInvitation doomed (sampleInvitation doomed "invitation-doomed" person)
  store.appendAudit doomed ⟨soon, .anonymous, .attemptCreated ⟨"attempt-doomed"⟩⟩
  let _ ← store.recordDeliveryFailure doomed person.normalise .hardBounce epoch "gone"
  store.recordConsent doomed ⟨⟨"account-doomed"⟩, terms, "2026-01", .granted, epoch⟩
  let _ ← store.createCredential doomed
    (sampleCredential doomed "cred-doomed" ⟨"account-doomed"⟩ sampleIdentity)
  store.createFederationState doomed (sampleState doomed "state-doomed" (digestOf [21]) later)
  store.createRecoveryGrant doomed
    (sampleRecoveryGrant doomed "grant-doomed" ⟨"account-doomed"⟩)
  store.deleteTenant doomed
  let doomedAccount ← store.accountByIdentity doomed person.normalise
  let doomedAttempt ← store.attemptById doomed ⟨"attempt-doomed"⟩
  let doomedSession ← store.sessionByDigest doomed soon (digestOf [20])
  let doomedInvitation ← store.invitationById doomed ⟨"invitation-doomed"⟩
  let doomedAudit ← store.auditEntries doomed
  let doomedRecord ← store.deliveryRecord doomed person.normalise
  let doomedConsent ← store.consentHistory doomed ⟨"account-doomed"⟩
  let doomedCredential ← store.credentialByIdentity doomed sampleIdentity
  let doomedState ← store.federationStateByDigest doomed epoch (digestOf [21])
  let doomedGrant ← store.recoveryGrantById doomed ⟨"grant-doomed"⟩
  let survivingAccount ← store.accountByIdentity alpha person.normalise

  -- Linked identities, keyed on issuer and subject and never on the address (AUTH-6.6).
  let linkOk ← store.createCredential alpha (sampleCredential alpha "cred-1" ⟨"account-1"⟩ sampleIdentity)
  let linkedBack ← store.credentialByIdentity alpha sampleIdentity
  let linkAgain ← store.createCredential alpha (sampleCredential alpha "cred-2" ⟨"account-3"⟩ sampleIdentity)
  let crossTenantCredential ← store.credentialByIdentity beta sampleIdentity
  let accountCredentials ← store.credentialsForAccount alpha ⟨"account-1"⟩
  store.deleteCredential alpha ⟨"cred-1"⟩
  let afterUnlink ← store.credentialByIdentity alpha sampleIdentity

  -- Additional verified addresses, and the uniqueness that spans them and the primary.
  let spare := addressOf "spare"
  let addSpare ← store.addVerifiedEmail alpha ⟨"account-1"⟩ spare.normalise
  let holderOfSpare ← store.accountByVerifiedEmail alpha spare.normalise
  let holderOfPrimary ← store.accountByVerifiedEmail alpha person.normalise
  let spareTakenByOther ← store.addVerifiedEmail alpha ⟨"account-3"⟩ spare.normalise
  let primaryTakenByOther ← store.addVerifiedEmail alpha ⟨"account-3"⟩ person.normalise
  let crossTenantVerified ← store.accountByVerifiedEmail beta spare.normalise
  store.removeVerifiedEmail alpha ⟨"account-1"⟩ spare.normalise
  let afterSpareRemoved ← store.accountByVerifiedEmail alpha spare.normalise

  -- The state record `state` is bound to: single use, expiring, and invisible across tenants.
  let liveStateDigest := digestOf [7, 1]
  let staleStateDigest := digestOf [7, 2]
  let racedDigest := digestOf [7, 3]
  store.createFederationState alpha (sampleState alpha "state-live" liveStateDigest later)
  store.createFederationState alpha (sampleState alpha "state-stale" staleStateDigest soon)
  store.createFederationState alpha (sampleState alpha "state-raced" racedDigest later)
  let liveState ← store.federationStateByDigest alpha epoch liveStateDigest
  let staleState ← store.federationStateByDigest alpha later staleStateDigest
  let crossTenantState ← store.federationStateByDigest beta epoch liveStateDigest
  -- Two callbacks read one record, then both write: exactly one may win (AUTH-6.2).
  let racedA ← store.federationStateByDigest alpha epoch racedDigest
  let racedB ← store.federationStateByDigest alpha epoch racedDigest
  let firstCommit ← match racedA with
    | some state => store.commitFederationState alpha state (state.consumed epoch)
    | none => pure false
  let secondCommit ← match racedB with
    | some state => store.commitFederationState alpha state (state.consumed epoch)
    | none => pure false
  let afterStateCommit ← store.federationStateByDigest alpha epoch racedDigest

  -- Passkeys: the credential and its attributes are written together, found by the id the
  -- authenticator gives back, and invisible to another tenant.
  let passkey : PasskeyId := ⟨"passkey-handle-1"⟩
  let passkeyWrite ← store.createPasskey alpha
    (samplePasskeyCredential alpha "credential-passkey" ⟨"account-1"⟩ passkey)
    (samplePasskey alpha "credential-passkey" "Laptop")
  let foundPasskey ← store.credentialByPasskey alpha passkey
  let crossTenantPasskey ← store.credentialByPasskey beta passkey
  let registration ← store.passkeyRegistration alpha ⟨"credential-passkey"⟩
  -- The same handle twice in one tenant is one credential (AUTH-15.4.2).
  let passkeyAgain ← store.createPasskey alpha
    (samplePasskeyCredential alpha "credential-passkey-2" ⟨"account-1"⟩ passkey)
    (samplePasskey alpha "credential-passkey-2" "Duplicate")
  store.setPasskeySignCount alpha ⟨"credential-passkey"⟩ 42
  let counted ← store.passkeyRegistration alpha ⟨"credential-passkey"⟩
  let listedPasskeys ← store.passkeysForAccount alpha ⟨"account-1"⟩
  -- Removing the credential takes its attributes with it, or the next credential given that id
  -- would inherit a key it never registered.
  store.deleteCredential alpha ⟨"credential-passkey"⟩
  let orphanedRegistration ← store.passkeyRegistration alpha ⟨"credential-passkey"⟩

  -- Ceremonies: expiring, single use under compare and set, and scoped to their tenant.
  let liveChallenge := digestOf [8, 1]
  let staleChallenge := digestOf [8, 2]
  let racedChallenge := digestOf [8, 3]
  store.createPasskeyCeremony alpha
    (samplePasskeyCeremony alpha "ceremony-live" liveChallenge later)
  store.createPasskeyCeremony alpha
    (samplePasskeyCeremony alpha "ceremony-stale" staleChallenge soon)
  store.createPasskeyCeremony alpha
    (samplePasskeyCeremony alpha "ceremony-raced" racedChallenge later)
  let liveCeremony ← store.passkeyCeremonyById alpha epoch ⟨"ceremony-live"⟩
  let staleCeremony ← store.passkeyCeremonyById alpha later ⟨"ceremony-stale"⟩
  let crossTenantCeremony ← store.passkeyCeremonyById beta epoch ⟨"ceremony-live"⟩
  let racedCeremonyA ← store.passkeyCeremonyById alpha epoch ⟨"ceremony-raced"⟩
  let racedCeremonyB ← store.passkeyCeremonyById alpha epoch ⟨"ceremony-raced"⟩
  let firstCeremonyCommit ← match racedCeremonyA with
    | some ceremony => store.commitPasskeyCeremony alpha ceremony (ceremony.consumed epoch)
    | none => pure false
  let secondCeremonyCommit ← match racedCeremonyB with
    | some ceremony => store.commitPasskeyCeremony alpha ceremony (ceremony.consumed epoch)
    | none => pure false
  let afterCeremonyCommit ← store.passkeyCeremonyById alpha epoch ⟨"ceremony-raced"⟩
  -- Sweeping reaches ceremonies, and reports what it took.
  store.createPasskeyCeremony swept
    (samplePasskeyCeremony swept "ceremony-swept" (digestOf [8, 4]) epoch)
  let purgedCeremonies ← store.purgeExpired swept soon

  -- Recovery grants: every field read back, single use under a race, and listed per account.
  store.createRecoveryGrant alpha (sampleRecoveryGrant alpha "grant-raced" account)
  store.createRecoveryGrant alpha
    { sampleRecoveryGrant alpha "grant-keep" account with disposition := .keepExisting }
  store.createRecoveryGrant alpha (sampleRecoveryGrant alpha "grant-other" ⟨"account-3"⟩)
  let readGrant ← store.recoveryGrantById alpha ⟨"grant-keep"⟩
  let crossTenantGrant ← store.recoveryGrantById beta ⟨"grant-keep"⟩
  let grantsHeld ← store.recoveryGrantsForAccount alpha account
  let racedGrantA ← store.recoveryGrantById alpha ⟨"grant-raced"⟩
  let racedGrantB ← store.recoveryGrantById alpha ⟨"grant-raced"⟩
  let firstGrantCommit ← match racedGrantA with
    | some held => store.commitRecoveryGrant alpha held (RecoveryGrant.markSpent soon held)
    | none => pure false
  let secondGrantCommit ← match racedGrantB with
    | some held => store.commitRecoveryGrant alpha held (RecoveryGrant.markSpent soon held)
    | none => pure false
  let afterGrantCommit ← store.recoveryGrantById alpha ⟨"grant-raced"⟩
  store.createRecoveryGrant swept
    { sampleRecoveryGrant swept "grant-swept" ⟨"account-swept"⟩ with expiresAt := epoch }
  store.createRecoveryGrant swept (sampleRecoveryGrant swept "grant-kept" ⟨"account-swept"⟩)
  let purgedGrants ← store.purgeExpired swept soon
  let sweptLiveGrant ← store.recoveryGrantById swept ⟨"grant-kept"⟩
  for event in everyAuditEvent logged do
    store.appendAudit logged ⟨soon, .client "admin", event⟩
  let loggedAudit ← store.auditEntries logged

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
    , { name := "an account is readable by its identifier"
        passed := (byId.map (·.identity)) == some person.normalise }
    , { name := "an account identifier does not resolve in another tenant"
        passed := crossTenantById.isNone }
    , { name := "changing the primary address moves the account to it (AUTH-9.6)"
        passed := renamed matches .ok _ && (underNewAddress.map (·.id.value)) == some "account-1"
          && underOldAddress.isNone }
    , { name := "an address another account already holds is refused (AUTH-15.4.2)"
        passed := collided matches .error .duplicateAccount }
    , { name := "changing the address of an account that does not exist is refused"
        passed := missing matches .error .unknownAccount }
    , { name := "the address can be changed back"
        passed := restored matches .ok _ }
    , { name := "deactivation is recorded on the account, which still exists"
        passed := deactivated matches .ok _
          && (afterDeactivation.map (·.status)) == some .deactivated }
    , { name := "deactivating an account that does not exist is refused"
        passed := statusOfMissing matches .error .unknownAccount }
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
        passed := (foundLive.toOption.map (·.id.value)) == some "session-live" }
    , { name := "a session past its idle timeout is refused, and says so (AUTH-15.4.3)"
        passed := refusalOf foundIdle == some .idleExpired }
    , { name := "a session past its absolute lifetime is refused, and says which"
        passed := refusalOf foundStale == some .absolutelyExpired }
    , { name := "a revoked session is refused as revoked and not as expired"
        passed := refusalOf foundRevoked == some .revoked }
    , { name := "a session is unknown from another tenant, not merely refused"
        passed := refusalOf crossTenantSession == some .unknown }
    , { name := "a session past its idle timeout is live again once touched (AUTH-9.4)"
        passed := refusalOf beforeTouch == some .idleExpired
          && (afterTouch.toOption.map (·.id.value)) == some "session-touch" }
    , { name := "touching does not reach past the absolute lifetime"
        passed := refusalOf touchedStale == some .absolutelyExpired }
    , { name := "an account's live sessions are listed, and only those"
        passed := ownSessions.length == 2 }
    , { name := "revoking an account's sessions revokes all of them (AUTH-9.6)"
        passed := afterMassRevoke.isEmpty }
    , { name := "an invitation can be accepted only once (AUTH-8.5)"
        passed := invitationCommits == some (true, false) }
    , { name := "a transient failure is counted and does not suppress (AUTH-12.5)"
        passed := !softOnce.suppressed && !softTwice.suppressed && softTwice.failures == 2
          && softOnce.firstFailureAt == softTwice.firstFailureAt }
    , { name := "a hard bounce suppresses the address (AUTH-12.1)"
        passed := hard.suppressedBy == some .hardBounce }
    , { name := "a later transient failure does not lift a suppression"
        passed := softAfterHard.suppressedBy == some .hardBounce
          && softAfterHard.failures == 2 }
    , { name := "delivery history does not cross tenants (AUTH-12.2)"
        passed := crossTenantRecord.isNone }
    , { name := "the tenant's delivery history is listed"
        passed := allRecords.length == 2 }
    , { name := "clearing a suppression clears the history with it (AUTH-12.4)"
        passed := afterClearing.isNone }
    , { name := "the client can suppress an address itself"
        passed := byClient.suppressedBy == some .client }
    , { name := "a withdrawal is another entry, not an edit to the one that granted (AUTH-4.6.3)"
        passed := consentTrail.map (fun entry => (entry.subject, entry.act)) ==
          [(terms, .granted), (marketing, .granted), (marketing, .withdrawn)] }
    , { name := "the version each answer was given under is kept (AUTH-4.6.2)"
        passed := consentTrail.map (·.version) == ["2026-01", "2026-01", "2026-01"] }
    , { name := "the last word decides where a subject stands (AUTH-4.6.4)"
        passed := !Consent.granted consentTrail marketing && Consent.granted consentTrail terms }
    , { name := "consent does not cross tenants"
        passed := crossTenantConsent.isEmpty }
    , { name := "an account that withdrew is not still consenting (AUTH-4.6.5)"
        passed := stillConsenting.map (·.value) == ["account-3"] }
    , { name := "consent in one tenant grants nothing in another"
        passed := consentingElsewhere.map (·.value) == ["account-1"] }
    , { name := "audit entries are readable in the tenant they were written for"
        passed := alphaAudit.length == 1 }
    , { name := "audit entries do not leak across tenants"
        passed := betaAudit.length == 1 }
    , { name := "sweeping removes an expired attempt and reports it (AUTH-15.4.3)"
        passed := sweptStaleAttempt.isNone && purged.attempts == 1 }
    , { name := "sweeping leaves a live attempt alone"
        passed := (sweptLiveAttempt.map (·.id.value)) == some "attempt-live" }
    , { name := "sweeping removes the sessions nothing can reach, and only those"
        passed := purged.sessions == 2
          && (sweptLiveSession.toOption.map (·.id.value)) == some "session-live" }
    , { name := "sweeping leaves the audit log and consent records where they are (AUTH-4.6.6)"
        passed := sweptAudit.length == 1 && sweptConsent.length == 1 }
    , { name := "deleting a tenant removes its accounts (AUTH-4.2.5)"
        passed := doomedAccount.isNone }
    , { name := "deleting a tenant removes its attempts"
        passed := doomedAttempt.isNone }
    , { name := "deleting a tenant removes its sessions"
        passed := refusalOf doomedSession == some .unknown }
    , { name := "deleting a tenant removes its invitations"
        passed := doomedInvitation.isNone }
    , { name := "deleting a tenant removes its audit records"
        passed := doomedAudit.isEmpty }
    , { name := "deleting a tenant removes its delivery history"
        passed := doomedRecord.isNone }
    , { name := "deleting a tenant removes its consent records (AUTH-4.2.5)"
        passed := doomedConsent.isEmpty }
    , { name := "deleting a tenant leaves other tenants alone"
        passed := survivingAccount.isSome }
    , { name := "a linked identity is readable by the issuer and subject it was created with (AUTH-6.6)"
        passed := linkOk.toOption.isSome && (linkedBack.map (·.account.value)) == some "account-1" }
    , { name := "one identity cannot be linked to two accounts (AUTH-15.4.2)"
        passed := refused .duplicateCredential linkAgain }
    , { name := "a linked identity is invisible from another tenant (AUTH-4.2.4)"
        passed := crossTenantCredential.isNone }
    , { name := "an account's credentials are listed, which is what AUTH-6.8 counts"
        passed := accountCredentials.length == 1 }
    , { name := "unlinking removes the credential"
        passed := afterUnlink.isNone }
    , { name := "an additional verified address finds its account (AUTH-6.7)"
        passed := addSpare.toOption.isSome && (holderOfSpare.map (·.id.value)) == some "account-1" }
    , { name := "a primary address is found by the same lookup"
        passed := (holderOfPrimary.map (·.id.value)) == some "account-1" }
    , { name := "an address verified on one account cannot be verified on another"
        passed := refused .duplicateEmail spareTakenByOther }
    , { name := "another account's primary cannot be claimed as an additional address"
        passed := refused .duplicateEmail primaryTakenByOther }
    , { name := "a verified address is invisible from another tenant (AUTH-4.2.4)"
        passed := crossTenantVerified.isNone }
    , { name := "removing a verified address removes it"
        passed := afterSpareRemoved.isNone }
    , { name := "a state record is readable by the digest of the state it was created with (AUTH-6.2)"
        passed := (liveState.map (·.verifier)) == some "verifier-state-live" }
    , { name := "and what the start bound to it: the invitation and the account (AUTH-6.7.1)"
        passed := (liveState.bind (·.account)) == some ⟨"account-state-live"⟩
          && (liveState.bind (·.invitation)) == some ⟨"invitation-state-live"⟩ }
    , { name := "an expired state record is refused on read (AUTH-15.4.3)"
        passed := staleState.isNone }
    , { name := "a state record is invisible from another tenant (AUTH-4.2.4)"
        passed := crossTenantState.isNone }
    , { name := "two callbacks racing with one state produce one sign-in (AUTH-6.2)"
        passed := firstCommit && !secondCommit }
    , { name := "a spent state record is refused on read"
        passed := afterStateCommit.isNone }
    , { name := "deleting a tenant removes its credentials (AUTH-4.2.5)"
        passed := doomedCredential.isNone }
    , { name := "deleting a tenant removes its state records (AUTH-4.2.5)"
        passed := doomedState.isNone }
    , { name := "a passkey credential is readable by the id the authenticator gives back"
        passed := passkeyWrite.isOk
          && (foundPasskey.map (·.id.value)) == some "credential-passkey" }
    , { name := "and carries the passkey id back as its descriptor"
        passed := (foundPasskey.map (·.descriptor)) == some (.passkey passkey) }
    , { name := "a passkey credential is invisible from another tenant (AUTH-4.2.4)"
        passed := crossTenantPasskey.isNone }
    , { name := "the attributes are written with the credential, not after it"
        passed := (registration.map (·.label)) == some "Laptop"
          && (registration.map (·.algorithm)) == some ⟨-7⟩
          && (registration.map (·.transports)) == some ["internal", "hybrid"]
          && (registration.map (·.backupEligible)) == some true }
    , { name := "one passkey id is one credential in a tenant (AUTH-15.4.2)"
        passed := match passkeyAgain with
          | .error .duplicateCredential => true
          | _ => false }
    , { name := "the counter an assertion reported is kept"
        passed := (counted.map (·.signCount)) == some 42 }
    , { name := "an account's passkeys are listed"
        passed := listedPasskeys.map (·.label) == ["Laptop"] }
    , { name := "removing a credential removes its attributes, leaving no orphan (AUTH-4.2.5)"
        passed := orphanedRegistration.isNone }
    , { name := "a ceremony is readable by the id its cookie names"
        passed := (liveCeremony.bind (·.account)) == some ⟨"account-ceremony-live"⟩ }
    , { name := "an expired ceremony is refused on read (AUTH-15.4.3)"
        passed := staleCeremony.isNone }
    , { name := "a ceremony is invisible from another tenant (AUTH-4.2.4)"
        passed := crossTenantCeremony.isNone }
    , { name := "two requests racing with one challenge produce one sign-in"
        passed := firstCeremonyCommit && !secondCeremonyCommit }
    , { name := "a spent ceremony is refused on read"
        passed := afterCeremonyCommit.isNone }
    , { name := "sweeping removes expired ceremonies and reports how many"
        passed := purgedCeremonies.passkeyCeremonies == 1 }
    , { name := "a recovery grant reads back as it was written, disposition included"
        passed := (readGrant.map (·.account.value)) == some "account-1"
          && (readGrant.map (·.disposition)) == some .keepExisting
          && (readGrant.map (·.state)) == some .pending
          && (readGrant.map (·.createdBy)) == some (.client "conformance")
          && (readGrant.map (·.tokenDigest)) == some (digestOf [4, 5]) }
    , { name := "a recovery grant is invisible from another tenant (AUTH-4.2.4)"
        passed := crossTenantGrant.isNone }
    , { name := "an account's grants are listed, and only its own (AUTH-9.10.7)"
        passed := (grantsHeld.map (·.id.value)).length == 2
          && !(grantsHeld.map (·.id.value)).contains "grant-other" }
    , { name := "two ceremonies racing to redeem one grant enrol once (AUTH-9.10.4)"
        passed := firstGrantCommit && !secondGrantCommit }
    , { name := "a spent grant reads back as spent rather than vanishing (AUTH-9.10.6)"
        passed := (afterGrantCommit.map (·.state)) == some .spent
          && (afterGrantCommit.bind (·.spentAt)) == some soon }
    , { name := "sweeping removes expired grants, and only those"
        passed := purgedGrants.recoveryGrants == 1 && sweptLiveGrant.isSome }
    , { name := "deleting a tenant removes its recovery grants"
        passed := doomedGrant.isNone }
    , { name := "every audit event reads back as what was written (AUTH-14.1.7)"
        passed := loggedAudit.map (·.event) == everyAuditEvent logged
          && loggedAudit.all (·.actor == .client "admin") } ]

end Authentication.Store.Conformance
