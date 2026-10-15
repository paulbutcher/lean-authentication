/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import AuthenticationPasskey
import AuthenticationSqlite

/-!
Registering a passkey and signing in with it, driven through the service against SQLite.

The authenticator is stood in for: a key OpenSSL generated, an `authenticatorData` built to the
layout, and an attestation object encoded with `lean-cbor`. What that cannot establish is that a
real device agrees about the layout, which is Phase 6's vectors. What it does establish is that
the ceremony holds together: the challenge a begin minted is the one a complete accepts, the
credential written is the one an assertion finds, and the session comes out of `issueFor` with
everything that implies.
-/

namespace Tests.PasskeyFlow
open Authentication Authentication.Service Authentication.Passkey

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

private def credentialId : ByteArray := ⟨#[9, 8, 7, 6, 5, 4, 3, 2, 1, 0, 1, 2, 3, 4, 5, 6]⟩

private def clientDataFor (type challenge : String) : String :=
  "{\"type\":\"" ++ type ++ "\",\"challenge\":\"" ++ challenge
    ++ "\",\"origin\":\"https://example.com\",\"crossOrigin\":false}"

private def coseKeyOf (x y : ByteArray) : ByteArray :=
  ((Cbor.Value.map?
      [ (Cose.ktyLabel, Cbor.Value.int Cose.ec2KeyType),
        (Cose.algLabel, Cbor.Value.int Cose.es256Algorithm),
        (Cose.crvLabel, Cbor.Value.int Cose.p256Curve),
        (Cose.xLabel, (Cbor.Value.bytes? x).getD .null),
        (Cose.yLabel, (Cbor.Value.bytes? y).getD .null) ]).getD .null).encode

/-- `0x41` is user presence and attested credential data; the counter is zero, which is what a
synced passkey reports. -/
private def registrationAuthData (coseKey : ByteArray) : ByteArray :=
  ((((Leancrypto.Sha256.hash rpId.toUTF8).push 0x41 ++ ⟨#[0, 0, 0, 0]⟩)
      ++ ByteArray.mk (Array.replicate 16 0))
      ++ ⟨#[0, UInt8.ofNat credentialId.size]⟩ ++ credentialId) ++ coseKey

private def attestationObjectOf (authData : ByteArray) : ByteArray :=
  ((Cbor.Value.map?
      [ (.ofText "fmt", (Cbor.Value.text? "none").getD .null),
        (.ofText "attStmt", (Cbor.Value.map? []).getD .null),
        (.ofText "authData", (Cbor.Value.bytes? authData).getD .null) ]).getD .null).encode

private def assertionAuthData (signCount : UInt32) : ByteArray :=
  (Leancrypto.Sha256.hash rpId.toUTF8).push 0x01
    ++ ⟨#[(signCount >>> 24).toUInt8, (signCount >>> 16).toUInt8,
          (signCount >>> 8).toUInt8, signCount.toUInt8]⟩

private def coordinatesOf (spki : ByteArray) : ByteArray × ByteArray :=
  (spki.extract (spki.size - 64) (spki.size - 32), spki.extract (spki.size - 32) spki.size)

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
  let handle : PasskeyId := ⟨Leancrypto.Codec.Base64Url.encodeString credentialId⟩
  let asserting ← Service.beginAuthentication ports config
  let assertOptions := asserting.toOption
  let assertCookie := (assertOptions.map (·.cookie.value)).getD ""
  let assertChallenge := (assertOptions.map (·.challenge.encoded)).getD ""
  let assertClientData := clientDataFor assertionType assertChallenge
  let authData := assertionAuthData 0
  let signature ← Libcrypto.Sign.sign (.ecdsa .sha256) key
    (authData ++ Leancrypto.Sha256.hash assertClientData.toUTF8)
  let signedIn ← Service.completeAuthentication ports verifier config assertCookie handle
    authData assertClientData signature
  let identified ← match signedIn.toOption.bind (·.session) with
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
      authData clientDataThere signatureThere

  let noRelyingParty ← Service.beginRegistration ports
    { config with passkeyRelyingParty := none } account

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
        | .ok outcome => outcome.session.isNone
            && outcome.views == [.refused .originNotPermitted]
        | .error _ => false),
      ("passkey flow: a tenant with no relying party offers no passkeys",
        match noRelyingParty with
        | .error .noRelyingParty => true
        | _ => false) ]

end Tests.PasskeyFlow
