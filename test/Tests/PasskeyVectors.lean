/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import AuthenticationPasskey
import Tests.Fixtures.PyWebauthn

/-!
The passkey verification against bytes this repository did not produce.

Three fixtures, and the third is the one that closes the loop.

`PyWebauthn` is a registration from a real device, redistributed, which settles the layout where
an off-by-one would hide; it carries no private key, so no signature over it can be checked.
`passkey-assertion.json` settles a signature, over bytes `make-passkey-fixtures.sh` laid out from
the specification rather than from this library, but against a key this repository made.

`passkey-capture.json` joins the two. `make-passkey-capture.mjs` drives Chrome's virtual
authenticator through a whole ceremony, and the key the assertion verifies against is the one
read out of its own registration, so nothing in the loop was laid out, keyed or signed here.
-/

namespace Tests.PasskeyVectors
open Authentication Authentication.Passkey

private def decode (text : String) : ByteArray :=
  (Leancrypto.Codec.Base64Url.decodeString text).getD ⟨#[]⟩

private def assertionJson : String := include_str "../fixtures/passkey-assertion.json"

private def captureJson : String := include_str "../fixtures/passkey-capture.json"

private def member (payload : Json) (name : String) : String :=
  ((payload.getObjVal? name).toOption.bind (·.getStr?.toOption)).getD ""

private def nested (payload : Json) (group name : String) : String :=
  match (payload.getObjVal? group).toOption with
  | some inner => member inner name
  | none => ""

/-- The `authData` out of an attestation object, which is the one step of the registration path
that is not public: `verifyRegistration` does it behind a `clientDataJSON` this capture has none
of. Three calls into `lean-cbor`, so what is exercised below is the layout and the COSE reading. -/
private def authDataOf (attestation : ByteArray) : Option ByteArray :=
  match Cbor.decode attestation with
  | .error _ => none
  | .ok value => (value.bytesAt (.ofText "authData")).toOption

def checks : IO (List (String × Bool)) := do
  -- A real authenticator's registration: the layout, and the key read out of it.
  let captured := decode Fixtures.PyWebauthn.noneAttestation
  let parsed := (authDataOf captured).map AuthData.parse
  let key := match parsed with
    | some (.ok data) =>
      data.attested.map fun (attested : AttestedCredential) => Cose.publicKeyInfo attested.coseKey
    | _ => none
  let loaded ← match key with
    | some (.ok (_, spki)) => do pure (← Libcrypto.Evp.PKey.fromSpki spki).isSome
    | _ => pure false

  -- A generated assertion: the signature, over bytes a shell script laid out.
  let fixture := (Json.parse assertionJson).toOption.getD .null
  let party : RelyingParty :=
    { id := member fixture "relyingPartyId", origins := [member fixture "origin"] }
  let challenge := member fixture "challenge"
  let authData := decode (member fixture "authenticatorData")
  let clientData :=
    match String.fromUTF8? (decode (member fixture "clientDataJSON")) with
    | some text => text
    | none => ""
  let signature := decode (member fixture "signature")
  let publicKey := decode (member fixture "publicKey")
  let accepts := fun (echoed : String) => echoed == challenge

  let verified ← Ceremony.verifyAssertion authData clientData accepts party publicKey signature
  -- One byte of the counter changed: the same signature over a different message.
  let tampered ← Ceremony.verifyAssertion (authData.set! 36 0x02) clientData accepts party
    publicKey signature

  pure
    [ ("passkey vectors: a real authenticator's hash of the relying party is where this reads it",
        match parsed with
        | some (.ok data) =>
          Leancrypto.bytesEqual data.rpIdHash
            (Leancrypto.Sha256.hash Fixtures.PyWebauthn.relyingPartyId.toUTF8)
        | _ => false),
      ("passkey vectors: its flags say user present and attested credential data",
        match parsed with
        | some (.ok data) =>
          data.flags.userPresent && data.flags.attestedCredentialData && !data.flags.extensionData
        | _ => false),
      ("passkey vectors: the attested credential data is read whole, with nothing left over",
        match parsed with
        | some (.ok data) =>
          (data.attested.map (·.aaguid.size)) == some 16
            && (data.attested.map (·.credentialId.size)) == some 64
        | _ => false),
      ("passkey vectors: the credential's key is ES256 and OpenSSL loads what this builds from it",
        match key with
        | some (.ok (algorithm, _)) => algorithm == (⟨Cose.es256Algorithm⟩ : CoseAlgorithm) && loaded
        | _ => false),
      ("passkey vectors: a signature made by openssl over bytes a script laid out verifies",
        match verified with
        | .ok assertion => assertion.signCount == 1 && assertion.userVerified == false
        | .error _ => false),
      ("passkey vectors: changing one byte of that message breaks it",
        match tampered with
        | .error .signatureInvalid => true
        | _ => false) ]

/--
The whole ceremony against one authenticator's own bytes (§18.3, AUTH-16.5).

What the two fixtures above leave open is the join between them: the capture carries no private
key, and the generated assertion verifies against a key this repository made. Here the key comes
out of a real registration and the signature checked against it comes from the same credential,
so nothing in the loop was laid out or signed here.

The relying party is `localhost` because WebAuthn treats it as a secure origin without a
certificate, which is also why the py_webauthn capture uses it.
-/
def captureChecks : IO (List (String × Bool)) := do
  let fixture := (Json.parse captureJson).toOption.getD .null
  let party : RelyingParty :=
    { id := member fixture "relyingPartyId", origins := [member fixture "origin"] }
  let registrationChallenge := member fixture "registrationChallenge"
  let assertionChallenge := member fixture "assertionChallenge"

  let textOf (encoded : String) : String :=
    (String.fromUTF8? (decode encoded)).getD ""

  let registered := Ceremony.verifyRegistration
    (decode (nested fixture "registration" "attestationObject"))
    (textOf (nested fixture "registration" "clientDataJSON"))
    (· == registrationChallenge) party

  let authData := decode (nested fixture "assertion" "authenticatorData")
  let clientData := textOf (nested fixture "assertion" "clientDataJSON")
  let signature := decode (nested fixture "assertion" "signature")

  -- The key is the registration's, which is the join the other two fixtures cannot make.
  let key := match registered with
    | .ok credential => credential.publicKey
    | .error _ => ⟨#[]⟩
  let asserted ← Ceremony.verifyAssertion authData clientData (· == assertionChallenge) party key
    signature
  -- The challenge the browser echoed, against one it never saw.
  let wrongChallenge ← Ceremony.verifyAssertion authData clientData
    (· == registrationChallenge) party key signature
  -- Byte 32 is the flags, and `0x01` keeps user presence set so the check that reaches is the
  -- signature rather than the flag it dropped.
  let tampered ← Ceremony.verifyAssertion (authData.set! 32 0x01) clientData
    (· == assertionChallenge) party key signature

  pure
    [ ("passkey capture: a real authenticator's registration verifies, as ES256",
        match registered with
        | .ok credential =>
          credential.algorithm == (⟨Cose.es256Algorithm⟩ : CoseAlgorithm)
            && credential.passkey.value == nested fixture "registration" "id"
        | .error _ => false),
      ("passkey capture: its assertion verifies against the key that registration carried",
        match asserted with
        | .ok assertion => assertion.userVerified
        | .error _ => false),
      ("passkey capture: the counter moved on between the two, so neither looks cloned",
        match registered, asserted with
        | .ok credential, .ok assertion =>
          !Passkey.regressed credential.signCount assertion.signCount
        | _, _ => false),
      ("passkey capture: the handle the assertion names is the one registration wrote",
        nested fixture "assertion" "id" == nested fixture "registration" "id"
          && nested fixture "assertion" "userHandle" == member fixture "userHandle"),
      ("passkey capture: the other ceremony's challenge is not accepted for this one",
        match wrongChallenge with
        | .error .challengeMismatch => true
        | _ => false),
      ("passkey capture: changing one flag byte breaks the signature",
        match tampered with
        | .error .signatureInvalid => true
        | _ => false) ]

end Tests.PasskeyVectors
