/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import AuthenticationPasskey
import AuthenticationSqlite
import Tests.Fixtures.Authenticator

/-!
Registering a passkey and signing in with it, driven through the service against SQLite.

The authenticator is stood in for by `Tests.Fixtures.Authenticator`. What that establishes is that
the ceremony holds together: the challenge a begin minted is the one a complete accepts, the
credential written is the one an assertion finds, and the session comes out of `issueFor` with
everything that implies.
-/

namespace Tests.PasskeyFlow
open Authentication Authentication.Service Authentication.Passkey
open Tests.Fixtures.Authenticator (coseKeyOf attestationObjectOf coordinatesOf handle)

initialize clockRef : IO.Ref Timestamp ← IO.mkRef ⟨1700000000⟩
initialize drawCounter : IO.Ref Nat ← IO.mkRef 0

instance : Clock IO where
  now := clockRef.get

instance : RandomBytes IO where
  draw count := do
    let index ← drawCounter.modifyGet fun n => (n, n + 1)
    pure (.ok ((Leancrypto.Sha256.hashUtf8 s!"passkey-seed-{index}").extract 0 count))

private def address (raw : String) : EmailAddress := (EmailAddress.parse raw).toOption.getD default

private def peppers : PepperRing :=
  { current := { keyId := ⟨"pepper-1"⟩, secret := Leancrypto.Sha256.hashUtf8 "passkey pepper" } }

private def portsOn (db : SQLite) : Ports IO :=
  { store := Sqlite.store db
    transport := EmailTransport.capturing (fun _ => pure ())
    responsePolicy := SignInResponsePolicy.silent IO
    limiter := RateLimiter.unlimited IO
    responseFloor := ResponseFloor.immediate IO
    humanCheck := HumanCheck.unchecked IO
    peppers }

private def tenant : TenantId := ⟨"pk"⟩
private def rpId : String := "example.com"

private def config : TenantConfig tenant :=
  { displayName := "Acme"
    baseUrl := ⟨"https://example.com"⟩
    sendingIdentity := { address := address "sign-in@example.com", displayName := "Acme" }
    signupPolicy := .unrestricted
    passkeyRelyingParty := some { id := rpId, origins := ["https://example.com"] } }

private def account : AccountId tenant := ⟨"account-1"⟩

private def clientDataFor : String → String → String :=
  Tests.Fixtures.Authenticator.clientDataFor "https://example.com"

private def registrationAuthData : ByteArray → ByteArray :=
  Tests.Fixtures.Authenticator.registrationAuthData rpId

private def assertionAuthData : UInt32 → ByteArray :=
  Tests.Fixtures.Authenticator.assertionAuthData rpId

def checks : IO (List (String × Bool)) := do
  let db ← Sqlite.openInMemory
  let ports := portsOn db
  let _ ← ports.store.createAccount tenant
    { id := account
      identity := (address "person@example.com").normalise
      primaryEmail := address "person@example.com"
      createdAt := ⟨1700000000⟩ }

  let key ← Libcrypto.Evp.PKey.generate "EC" #[⟨"group", .utf8 "P-256"⟩]
  let spki ← key.toSpki
  let (x, y) := coordinatesOf spki

  -- Registration: begin, then complete with what an authenticator would have returned.
  let begun ← Service.beginRegistration ports config account
  let options := begun.toOption
  let cookie := (options.map (·.cookie.value)).getD ""
  let registrationChallenge := (options.map (·.challenge.encoded)).getD ""
  let attestation := attestationObjectOf (registrationAuthData (coseKeyOf x y))
  let registered ← Service.completeRegistration ports config account cookie attestation
    (clientDataFor registrationType registrationChallenge) "Laptop" ["internal"]
  -- The ceremony is spent, so the same message cannot register a second credential.
  let replayed ← Service.completeRegistration ports config account cookie attestation
    (clientDataFor registrationType registrationChallenge) "Laptop" ["internal"]

  let listed ← passkeys ports account
  let renamed ← renamePasskey ports account ((listed[0]?.map (·.credential)).getD ⟨""⟩) "Phone"
  let afterRename ← passkeys ports account

  -- Authentication: begin, sign what the authenticator would sign, complete.
  let asserting ← Service.beginAuthentication ports config
  let assertOptions := asserting.toOption
  let assertCookie := (assertOptions.map (·.cookie.value)).getD ""
  let assertChallenge := (assertOptions.map (·.challenge.encoded)).getD ""
  let assertClientData := clientDataFor assertionType assertChallenge
  let authData := assertionAuthData 0
  let signature ← Libcrypto.Sign.sign (.ecdsa .sha256) key
    (authData ++ Leancrypto.Sha256.hash assertClientData.toUTF8)
  let signedIn ← Service.completeAuthentication ports verifier config assertCookie handle
    (some (Passkey.userHandle account)) authData assertClientData signature
  let identified ← match signedIn.toOption.bind (·.outcome.session) with
    | some credential => Except.toOption <$> identify ports config credential
    | none => pure none

  -- A tenant that admits only its provider refuses a passkey like any other origin.
  let refusedByPolicy ← do
    let other ← Sqlite.openInMemory
    let otherPorts := portsOn other
    let otherConfig := { config with originPolicy := .only [.federatedIdentity] }
    let _ ← otherPorts.store.createAccount tenant
      { id := account
        identity := (address "person@example.com").normalise
        primaryEmail := address "person@example.com"
        createdAt := ⟨1700000000⟩ }
    let begunThere ← Service.beginRegistration otherPorts otherConfig account
    let cookieThere := ((begunThere.toOption).map (·.cookie.value)).getD ""
    let challengeThere := ((begunThere.toOption).map (·.challenge.encoded)).getD ""
    let _ ← Service.completeRegistration otherPorts otherConfig account cookieThere attestation
      (clientDataFor registrationType challengeThere) "Laptop" []
    let assertingThere ← Service.beginAuthentication otherPorts otherConfig
    let assertCookieThere := ((assertingThere.toOption).map (·.cookie.value)).getD ""
    let assertChallengeThere := ((assertingThere.toOption).map (·.challenge.encoded)).getD ""
    let clientDataThere := clientDataFor assertionType assertChallengeThere
    let signatureThere ← Libcrypto.Sign.sign (.ecdsa .sha256) key
      (authData ++ Leancrypto.Sha256.hash clientDataThere.toUTF8)
    Service.completeAuthentication otherPorts verifier otherConfig assertCookieThere handle
      (some (Passkey.userHandle account)) authData clientDataThere signatureThere

  let noRelyingParty ← Service.beginRegistration ports
    { config with passkeyRelyingParty := none } account

  -- A handle naming an account other than the credential's must not sign in, however good the
  -- signature over it is. Its own ceremony, because the one above is spent.
  let forHandle ← Service.beginAuthentication ports config
  let handleCookie := ((forHandle.toOption).map (·.cookie.value)).getD ""
  let handleChallenge := ((forHandle.toOption).map (·.challenge.encoded)).getD ""
  let handleClientData := clientDataFor assertionType handleChallenge
  let handleSignature ← Libcrypto.Sign.sign (.ecdsa .sha256) key
    (authData ++ Leancrypto.Sha256.hash handleClientData.toUTF8)
  let wrongHandle ← Service.completeAuthentication ports verifier config handleCookie handle
    (some "somebody-else") authData handleClientData handleSignature

  pure
    [ ("passkey flow: a registration begins with a challenge and a cookie",
        !registrationChallenge.isEmpty && cookie.contains ':'),
      ("passkey flow: the credential registered is the one the authenticator reported",
        match registered with
        | .ok registration => registration.label == "Laptop"
            && registration.transports == ["internal"] && registration.publicKey == spki
        | .error _ => false),
      ("passkey flow: the ceremony is spent, so the same message registers nothing more",
        match replayed with
        | .error .unknownCeremony => true
        | _ => false),
      ("passkey flow: the account's passkeys are listed, and renaming one takes",
        listed.length == 1 && renamed && afterRename.map (·.label) == ["Phone"]),
      ("passkey flow: an assertion signed by the registered key signs the account in",
        (identified.map (·.account)) == some account),
      ("passkey flow: the counter the assertion reported is kept",
        (afterRename[0]?.map (·.signCount)) == some 0),
      ("passkey flow: a tenant admitting only its provider refuses a passkey sign-in",
        match refusedByPolicy with
        | .ok completed => completed.outcome.session.isNone
            && completed.outcome.views == [.refused .originNotPermitted]
        | .error _ => false),
      ("passkey flow: a user handle naming another account does not sign in",
        match wrongHandle with
        | .error (.decided .userHandleMismatch) => true
        | _ => false),
      ("passkey flow: a tenant with no relying party offers no passkeys",
        match noRelyingParty with
        | .error .noRelyingParty => true
        | _ => false) ]

/-! ## Recovery

Registering a passkey with no session at all, which is the case a passkey-only tenant had no
answer to: the device holding the account's one credential is gone, so there is nothing to sign
in with and nothing to begin an ordinary registration from.
-/

private def holder : Account tenant :=
  { id := account
    identity := (address "person@example.com").normalise
    primaryEmail := address "person@example.com"
    createdAt := ⟨1700000000⟩ }

private def existingIdentity : FederatedIdentity := ⟨"https://issuer.example", "subject-1"⟩

/-- An account holding one federated identity, so a disposition has something to act on. -/
private def recoverable : IO SQLite := do
  let db ← Sqlite.openInMemory
  let ports := portsOn db
  let _ ← ports.store.createAccount tenant holder
  let _ ← ports.store.createCredential tenant
    { id := ⟨"cred-sso"⟩
      account
      descriptor := .federatedIdentity existingIdentity
      createdAt := ⟨1700000000⟩ }
  pure db

private def grantOf (issued : Except RecoveryRefusal (RecoveryIssued tenant)) :
    RecoveryGrantId tenant × CredentialValue :=
  match issued with
  | .ok made => (made.grant.id, made.token)
  | .error _ => (⟨""⟩, ⟨""⟩)

/-- One whole recovery onto a new passkey, answering what the account holds afterwards. The
attestation is built from a key generated here, as the registration above is. -/
private def recoverOnto (disposition : RecoveryDisposition) : IO (List (Credential tenant)) := do
  let ports := portsOn (← recoverable)
  let key ← Libcrypto.Evp.PKey.generate "EC" #[⟨"group", .utf8 "P-256"⟩]
  let (x, y) := coordinatesOf (← key.toSpki)
  let attestation := attestationObjectOf (registrationAuthData (coseKeyOf x y))
  let (grant, token) := grantOf (← createRecovery ports config account (disposition := disposition))
  let begun := (← Service.beginRecoveryRegistration ports config grant token).toOption
  let _ ← Service.completeRecoveryRegistration ports config
    ((begun.map (·.cookie.value)).getD "") attestation
    (clientDataFor registrationType ((begun.map (·.challenge.encoded)).getD ""))
    "Replacement" []
  ports.store.credentialsForAccount tenant account

def recoveryChecks : IO (List (String × Bool)) := do
  let ports := portsOn (← recoverable)
  let key ← Libcrypto.Evp.PKey.generate "EC" #[⟨"group", .utf8 "P-256"⟩]
  let (x, y) := coordinatesOf (← key.toSpki)
  let attestation := attestationObjectOf (registrationAuthData (coseKeyOf x y))

  let (grant, token) := grantOf (← createRecovery ports config account)

  -- Begun and walked away from. The grant has to survive that, or the person who fumbles the
  -- authenticator dialog needs another trip to an administrator.
  let _ ← Service.beginRecoveryRegistration ports config grant token
  let afterAbandoning ← authoriseRecovery (tenant := tenant) ports grant token

  let begun := (← Service.beginRecoveryRegistration ports config grant token).toOption
  let cookie := (begun.map (·.cookie.value)).getD ""
  let clientData := clientDataFor registrationType ((begun.map (·.challenge.encoded)).getD "")
  let registered ← Service.completeRecoveryRegistration ports config cookie attestation
    clientData "Replacement" []
  let afterSpending ← authoriseRecovery (tenant := tenant) ports grant token
  let audited ← ports.store.auditEntries tenant
  let signedIn ← Service.beginAuthentication ports config

  -- A second grant, revoked after its ceremony began: the enrolment is refused at the end.
  let (withdrawn, withdrawnToken) := grantOf (← createRecovery ports config account)
  let secondBegun :=
    (← Service.beginRecoveryRegistration ports config withdrawn withdrawnToken).toOption
  let _ ← revokeRecovery (tenant := tenant) ports withdrawn
  let afterRevoking ← Service.completeRecoveryRegistration ports config
    ((secondBegun.map (·.cookie.value)).getD "") attestation
    (clientDataFor registrationType ((secondBegun.map (·.challenge.encoded)).getD ""))
    "Too late" []

  let refusedAtBegin ←
    Service.beginRecoveryRegistration ports config grant ⟨"not-the-token"⟩

  let afterRemoving ← recoverOnto .removeExisting
  let afterKeeping ← recoverOnto .keepExisting

  pure
    [ ("recovery: a passkey registers with no session, on the grant alone (AUTH-9.10.2)",
        registered.toOption.isSome),
      ("recovery: beginning does not spend the grant, so an abandoned ceremony costs nothing",
        afterAbandoning.toOption.isSome),
      ("recovery: completing spends it, and a second enrolment has nothing to redeem",
        afterSpending.toOption.isNone),
      ("recovery: the redemption is audited against the account it enrolled onto",
        audited.any fun entry =>
          match entry.event with
          | .recoveryRedeemed enrolled _ => enrolled == account
          | _ => false),
      ("recovery: the account can start an authentication again afterwards",
        signedIn.toOption.isSome),
      ("recovery: a grant revoked mid-ceremony enrols nothing (AUTH-9.10.4)",
        match afterRevoking with
        | .error .recoveryRefused => true
        | _ => false),
      ("recovery: a wrong token is refused before any ceremony begins",
        match refusedAtBegin with
        | .error .recoveryRefused => true
        | _ => false),
      ("recovery: removing leaves exactly the passkey just enrolled",
        afterRemoving.map (·.descriptor.kind) == [.passkey]),
      ("recovery: keeping leaves what the account already had beside it",
        afterKeeping.length == 2
          && (afterKeeping.map (·.descriptor.kind)).contains .federatedIdentity) ]

end Tests.PasskeyFlow
