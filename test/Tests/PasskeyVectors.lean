/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import AuthenticationPasskey
import Tests.Fixtures.PyWebauthn

/-!
The passkey verification against bytes this repository did not produce.

Two fixtures, because no single one can cover both halves. The capture from a real authenticator
settles the layout, which is where an off-by-one would hide, and carries no private key so no
signature over it can be checked. The generated one settles the signature, and its bytes are laid
out by `make-passkey-fixtures.sh` from the specification's offsets rather than by this library, so
agreeing with it is not this library agreeing with itself.

What neither settles is in `KNOWN_ISSUES.md`: nothing here has run against a device this library
has not been shown the output of.
-/

namespace Tests.PasskeyVectors
open Authentication Authentication.Passkey

private def decode (text : String) : ByteArray :=
  (Leancrypto.Codec.Base64Url.decodeString text).getD ⟨#[]⟩

private def assertionJson : String := include_str "../fixtures/passkey-assertion.json"

private def member (payload : Json) (name : String) : String :=
  ((payload.getObjVal? name).toOption.bind (·.getStr?.toOption)).getD ""

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

end Tests.PasskeyVectors
