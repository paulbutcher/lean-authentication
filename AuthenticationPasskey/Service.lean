/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import AuthenticationPasskey.Ceremony

/-!
The four operations a client drives a passkey with.

They live here rather than in `Authentication.Service` for the reason `beginFederated` does: they
reach verification, and verification links OpenSSL. What is decided afterwards goes through
`Service.issueFor`, so a passkey sign-in gets the origin policy, the deactivation check, the audit
record and the session cookie rather than its own copies of them.

Nothing here renders. A begin answers with the values a page needs to call `navigator.credentials`
and leaves the JSON, and the script, to the client.
-/

public section

namespace Authentication.Passkey

/-- Why an operation did not get as far as a verdict on the message. Held apart from
`PasskeyError`, which is about the message; these are about the ceremony around it. -/
inductive CeremonyRefusal where
  /-- The random source would not produce a challenge. -/
  | noRandomness
  /-- No live ceremony has that id: it expired, it was spent, or the cookie named nothing. -/
  | unknownCeremony
  /-- The cookie did not carry the nonce the ceremony was created with, so this is not the browser
  that began it. -/
  | notOriginatingBrowser
  /-- A registration ceremony was offered to complete an assertion, or the reverse. -/
  | wrongCeremony
  /-- The ceremony was begun for an account other than the one now asking. -/
  | notThisAccount
  /-- The assertion named a handle this tenant holds no credential for. -/
  | unknownCredential
  /-- The message did not verify. -/
  | rejected (reason : PasskeyError)
  /-- The message verified and `Passkey.decide` refused it anyway, which is the user handle
  naming an account other than the credential's. -/
  | decided (reason : PasskeyRefusal)
  | notStored (reason : StoreError)
  /-- The tenant has configured no relying party, so it offers no passkeys. Refused rather than
  defaulted, because an identifier guessed here would be bound into every credential registered
  under it and could not be corrected afterwards. -/
  | noRelyingParty
  /-- The recovery grant this registration was offered under is not one that may be redeemed:
  spent, revoked, expired, no such grant, or the wrong token. One answer for all of them, as an
  invitation has, so that holding an identifier reports nothing about it. -/
  | recoveryRefused
  deriving Repr

def CeremonyRefusal.name : CeremonyRefusal → String
  | .noRandomness => "no-randomness"
  | .unknownCeremony => "unknown-ceremony"
  | .notOriginatingBrowser => "not-originating-browser"
  | .wrongCeremony => "wrong-ceremony"
  | .notThisAccount => "not-this-account"
  | .unknownCredential => "unknown-credential"
  | .rejected reason => reason.name
  | .decided reason => reason.name
  | .notStored _ => "not-stored"
  | .noRelyingParty => "no-relying-party"
  | .recoveryRefused => "recovery-refused"

/-- What a page needs to call `navigator.credentials.create`, as values rather than as JSON. -/
structure RegistrationOptions where
  challenge : CredentialValue
  /-- What goes on the authenticator: the account's own identifier (`Passkey.userHandle`). -/
  userHandle : String
  /-- The account's primary address, which WebAuthn requires the options to name and which is
  shown in the account picker on the person's own device. -/
  userName : String
  relyingParty : RelyingParty
  /-- The handles already on this account, so an authenticator holding one declines rather than
  registering a second credential for the same person. -/
  exclude : List PasskeyId
  cookie : CookieSpec

/-- What a page needs to call `navigator.credentials.get`. No credentials are named: this library
registers discoverable credentials only, so the authenticator offers what it holds and the
assertion carries the handle. -/
structure AssertionOptions where
  challenge : CredentialValue
  relyingParty : RelyingParty
  cookie : CookieSpec

namespace Service

open Authentication.Service

private def draw {m : Type → Type} [Monad m] [RandomBytes m] (bytes : Nat) :
    m (Option CredentialValue) := do
  match ← RandomBytes.draw bytes with
  | .error _ => pure none
  | .ok drawn => pure (some ⟨Leancrypto.Codec.Base64Url.encodeString drawn⟩)

private def partyOf {tenant : TenantId} (config : TenantConfig tenant) :
    Except CeremonyRefusal RelyingParty :=
  match config.passkeyRelyingParty with
  | none => .error .noRelyingParty
  | some party => .ok party

private def beginCeremony {m : Type → Type} [Monad m] [Clock m] [RandomBytes m]
    {tenant : TenantId} (ports : Ports m) (config : TenantConfig tenant)
    (kind : PasskeyCeremonyKind) (account : Option (AccountId tenant))
    (returnTo : Option String) (recovery : Option (RecoveryGrantId tenant) := none) :
    m (Except CeremonyRefusal (CredentialValue × CookieSpec)) := do
  let now ← Clock.now
  match ← draw 32, ← draw 16, ← draw 12 with
  | some challenge, some nonce, some identifier =>
    let expiresAt := now.advance PasskeyCeremony.maxLifetime
    let id : PasskeyCeremonyId tenant := ⟨identifier.encoded⟩
    ports.store.createPasskeyCeremony tenant
      { id
        kind
        challenge := ports.peppers.current.digest challenge
        bindingNonce := ports.peppers.current.digest nonce
        account
        recovery
        returnTo
        createdAt := now
        expiresAt }
    pure (.ok (challenge,
      CookieSpec.forPasskeyCeremony config.baseUrl tenant
        (PasskeyCeremony.cookieValue id nonce) expiresAt))
  | _, _, _ => pure (.error .noRandomness)

private def registrationFor {m : Type → Type} [Monad m] [Clock m] [RandomBytes m]
    {tenant : TenantId} (ports : Ports m) (config : TenantConfig tenant)
    (account : AccountId tenant) (recovery : Option (RecoveryGrantId tenant)) :
    m (Except CeremonyRefusal RegistrationOptions) := do
  match partyOf config with
  | .error refusal => pure (.error refusal)
  | .ok party =>
    match ← beginCeremony ports config .registration (some account) none recovery with
    | .error refusal => pure (.error refusal)
    | .ok (challenge, cookie) =>
      let held ← ports.store.credentialsForAccount tenant account
      let holder ← ports.store.accountById tenant account
      pure (.ok
        { challenge
          userHandle := Passkey.userHandle account
          userName := holder.map (·.primaryEmail.render) |>.getD ""
          relyingParty := party
          exclude := held.filterMap fun credential =>
            match credential.descriptor with
            | .passkey handle => some handle
            | _ => none
          cookie })

/-- Begins a registration for an account that is already signed in. The account comes from the
caller's session and is carried on the ceremony record, so completion cannot be told which account
to attach a credential to (AUTH-6.7.1 takes the same position for a federated link). -/
def beginRegistration {m : Type → Type} [Monad m] [Clock m] [RandomBytes m] {tenant : TenantId}
    (ports : Ports m) (config : TenantConfig tenant) (account : AccountId tenant) :
    m (Except CeremonyRefusal RegistrationOptions) :=
  registrationFor ports config account none

/--
Begins a registration authorised by a recovery grant rather than by a session (AUTH-9.10.2).

This is the whole point of a grant: the person has lost what they signed in with, so there is no
session to read an account from, and the account comes from the grant instead. The grant is
checked and not spent here, so a ceremony the authenticator refuses leaves it usable.

Nothing about the origin policy is consulted, for the reason AUTH-9.9.5 gives and which applies
unchanged: registering a credential issues no session. The sign-in that follows is checked like
any other, and on a tenant admitting only passkeys it is the passkey just registered that passes
it.
-/
def beginRecoveryRegistration {m : Type → Type} [Monad m] [Clock m] [RandomBytes m]
    {tenant : TenantId} (ports : Ports m) (config : TenantConfig tenant)
    (grant : RecoveryGrantId tenant) (token : CredentialValue) :
    m (Except CeremonyRefusal RegistrationOptions) := do
  match ← authoriseRecovery ports grant token with
  | .error _ => pure (.error .recoveryRefused)
  | .ok authorised =>
    registrationFor ports config authorised.account (some authorised.grant)

/-- Begins an authentication. No account is named and none is known: a discoverable credential is
what the authenticator offers, and which account it belongs to is settled by the assertion. -/
def beginAuthentication {m : Type → Type} [Monad m] [Clock m] [RandomBytes m] {tenant : TenantId}
    (ports : Ports m) (config : TenantConfig tenant) (returnTo : Option String := none) :
    m (Except CeremonyRefusal AssertionOptions) := do
  match partyOf config with
  | .error refusal => pure (.error refusal)
  | .ok party =>
    match ← beginCeremony ports config .authentication none returnTo with
    | .error refusal => pure (.error refusal)
    | .ok (challenge, cookie) => pure (.ok { challenge, relyingParty := party, cookie })

/-- The ceremony the cookie names, checked against the cookie's nonce and the kind expected. The
nonce is what makes holding a ceremony id insufficient. -/
private def liveCeremony {m : Type → Type} [Monad m] [Clock m] {tenant : TenantId}
    (ports : Ports m) (kind : PasskeyCeremonyKind) (cookie : String) :
    m (Except CeremonyRefusal (PasskeyCeremony tenant)) := do
  let now ← Clock.now
  match cookie.splitOn ":" with
  | [identifier, nonce] =>
    match ← ports.store.passkeyCeremonyById tenant now ⟨identifier⟩ with
    | none => pure (.error .unknownCeremony)
    | some ceremony =>
      if !ceremony.bindingNonce.accepts (ports.peppers.present ⟨nonce⟩) then
        pure (.error .notOriginatingBrowser)
      else if ceremony.kind != kind then pure (.error .wrongCeremony)
      else pure (.ok ceremony)
  | _ => pure (.error .unknownCeremony)

/-- Digests the challenge the browser echoed under every live pepper and compares it with the one
the ceremony holds. This is the only way the clear value is ever tested: a ceremony keeps a digest,
as every credential here does, so the comparison is `Digest.accepts` and constant time. -/
private def challengeAccepts {m : Type → Type} {tenant : TenantId} (ports : Ports m)
    (ceremony : PasskeyCeremony tenant) : String → Bool :=
  fun echoed => ceremony.challenge.accepts (ports.peppers.present ⟨echoed⟩)

/--
Completes a registration, whichever of the two began it.

`expected` is the account the caller holds a session for, and `none` where it holds a recovery
grant instead: the account is the ceremony's either way, and the parameter only says whether the
caller is entitled to the one it names. A ceremony carrying a grant redeems it here however it
is completed, so presenting a recovery cookie to the session route does not enrol a credential
while leaving the grant pending.

The order is forced. The ceremony is spent under compare and set, then the grant, and only then
is the credential written: either race resolved after the write would be a credential nobody
authorised. The disposition is applied last, once there is something for the account to be left
with.
-/
private def finishRegistration {m : Type → Type} [Monad m] [Clock m] [RandomBytes m]
    {tenant : TenantId} (ports : Ports m) (config : TenantConfig tenant)
    (expected : Option (AccountId tenant)) (cookie : String) (attestationObject : ByteArray)
    (clientDataJson label : String) (transports : List String) :
    m (Except CeremonyRefusal (PasskeyRegistration tenant)) := do
  match partyOf config with
  | .error refusal => pure (.error refusal)
  | .ok party =>
    match ← liveCeremony ports .registration cookie with
    | .error refusal => pure (.error refusal)
    | .ok ceremony =>
      match ceremony.account with
      | none => pure (.error .notThisAccount)
      | some account =>
      if expected.isSome && expected != some account then pure (.error .notThisAccount)
      else
        match Ceremony.verifyRegistration attestationObject clientDataJson
            (challengeAccepts ports ceremony) party with
        | .error reason => pure (.error (.rejected reason))
        | .ok registered => do
          let now ← Clock.now
          if !(← ports.store.commitPasskeyCeremony tenant ceremony (ceremony.consumed now)) then
            pure (.error .unknownCeremony)
          else
            match ← (match ceremony.recovery with
                | none => pure (some none)
                | some grant => (·.map some) <$> spendRecovery ports grant) with
            | none => pure (.error .recoveryRefused)
            | some redeemed =>
            match ← draw 12 with
            | none => pure (.error .noRandomness)
            | some identifier =>
              let credential : CredentialId tenant := ⟨identifier.encoded⟩
              let registration : PasskeyRegistration tenant :=
                { credential
                  publicKey := registered.publicKey
                  algorithm := registered.algorithm
                  signCount := registered.signCount
                  transports
                  aaguid := registered.aaguid
                  backupEligible := registered.backupEligible
                  backupState := registered.backupState
                  label
                  createdAt := now }
              match ← ports.store.createPasskey tenant
                  { id := credential
                    account
                    descriptor := .passkey registered.passkey
                    createdAt := now } registration with
              | .error reason => pure (.error (.notStored reason))
              | .ok () =>
                ports.store.appendAudit tenant
                  ⟨now, .anonymous, .identityLinked account "passkey"⟩
                if let some authorised := redeemed then
                  applyRecoveryDisposition ports authorised.disposition account credential
                pure (.ok registration)

/--
Completes a registration begun by an account that is signed in.

`label` and `transports` are the client's, because an authenticator names neither.
-/
def completeRegistration {m : Type → Type} [Monad m] [Clock m] [RandomBytes m]
    {tenant : TenantId} (ports : Ports m) (config : TenantConfig tenant)
    (account : AccountId tenant) (cookie : String) (attestationObject : ByteArray)
    (clientDataJson label : String) (transports : List String := []) :
    m (Except CeremonyRefusal (PasskeyRegistration tenant)) :=
  finishRegistration ports config (some account) cookie attestationObject clientDataJson label
    transports

/-- Completes one begun under a recovery grant. There is no account to pass: the caller holds no
session, and the account is the grant's, carried on the ceremony since it began (AUTH-9.10.3). -/
def completeRecoveryRegistration {m : Type → Type} [Monad m] [Clock m] [RandomBytes m]
    {tenant : TenantId} (ports : Ports m) (config : TenantConfig tenant) (cookie : String)
    (attestationObject : ByteArray) (clientDataJson label : String)
    (transports : List String := []) :
    m (Except CeremonyRefusal (PasskeyRegistration tenant)) :=
  finishRegistration ports config none cookie attestationObject clientDataJson label transports

/-- What a completed authentication produced, and where its ceremony asked to land. The target is
still the tenant's to allow, and `TenantConfig.returnTo` is what allows it (AUTH-9.8). -/
structure PasskeySignIn (tenant : TenantId) where
  outcome : Outcome tenant
  returnTo : Option String

/--
Completes an authentication and issues a session.

The counter is recorded whatever it says, and a regression is audited rather than refused, for the
reason `Passkey.regressed` gives. The session comes from `Service.issueFor`, so the origin policy
and the deactivation check apply here as they do to every other way in.
-/
def completeAuthentication {m : Type → Type} [Monad m] [Clock m] [RandomBytes m]
    {tenant : TenantId} (ports : Ports m) (verifier : Verifier m) (config : TenantConfig tenant)
    (cookie : String) (handle : PasskeyId) (userHandle : Option String)
    (authenticatorData : ByteArray) (clientDataJson : String) (signature : ByteArray)
    (requester : RequestContext := {}) :
    m (Except CeremonyRefusal (PasskeySignIn tenant)) := do
  match partyOf config with
  | .error refusal => pure (.error refusal)
  | .ok party =>
    match ← liveCeremony ports .authentication cookie with
    | .error refusal => pure (.error refusal)
    | .ok ceremony =>
      match ← ports.store.credentialByPasskey tenant handle with
      | none => pure (.error .unknownCredential)
      | some credential =>
        match ← ports.store.passkeyRegistration tenant credential.id with
        | none => pure (.error .unknownCredential)
        | some stored =>
          match Ceremony.checkAssertion authenticatorData clientDataJson
              (challengeAccepts ports ceremony) party with
          | .error reason => pure (.error (.rejected reason))
          | .ok (verified, signingInput) =>
            match Passkey.decide
                { passkey := handle, userHandle, signCount := verified.signCount }
                (some credential) with
            | .refuse reason => pure (.error (.decided reason))
            | .signIn _ =>
            match ← verifier.verify stored.algorithm stored.publicKey signingInput signature with
            | .error reason => pure (.error (.rejected reason))
            | .ok () => do
              let now ← Clock.now
              if !(← ports.store.commitPasskeyCeremony tenant ceremony (ceremony.consumed now))
                then pure (.error .unknownCeremony)
              else do
                if Passkey.regressed stored.signCount verified.signCount then
                  ports.store.appendAudit tenant
                    ⟨now, .anonymous,
                      .passkeyCounterRegressed credential.account verified.signCount⟩
                ports.store.setPasskeySignCount tenant credential.id verified.signCount
                match ← ports.store.accountById tenant credential.account with
                | none => pure (.error .unknownCredential)
                | some existing =>
                  let outcome ← issueFor ports config
                    { origin := .passkey handle
                      address := existing.primaryEmail
                      requester }
                  pure (.ok { outcome, returnTo := ceremony.returnTo })

end Service

end Authentication.Passkey
