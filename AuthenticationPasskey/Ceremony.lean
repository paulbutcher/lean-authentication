/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import AuthenticationPasskey.AuthData
public import AuthenticationPasskey.ClientData
public import AuthenticationPasskey.Cose
import Libcrypto.Sign

/-!
The two ceremonies, checked end to end.

Everything a decision rests on is settled in the pure functions here; `verifyAssertion` adds only
the signature, which is the one step that needs a key loaded. A registration needs no signature at
all, because the only thing signed in one is the attestation statement and this library verifies
none (see `KNOWN_ISSUES.md`), so the whole of a registration is decided without an effect.
-/

public section

namespace Authentication.Passkey

def fmtKey : Cbor.Key := .ofText "fmt"
def attStmtKey : Cbor.Key := .ofText "attStmt"
def authDataKey : Cbor.Key := .ofText "authData"

/-- What a registration yields, less the parts only the client knows: a label for the credential
and the transports the browser reported. -/
structure RegisteredPasskey where
  passkey : PasskeyId
  publicKey : ByteArray
  algorithm : CoseAlgorithm
  signCount : UInt32
  aaguid : ByteArray
  backupEligible : Bool
  backupState : Bool
  userVerified : Bool
  /-- The attestation format the authenticator named. Recorded rather than acted on: nothing here
  verifies an attestation statement. -/
  format : String

/-- What an assertion yields once it has verified. The counter is the caller's to compare against
the stored one with `Passkey.regressed`. -/
structure VerifiedAssertion where
  signCount : UInt32
  userVerified : Bool
  backupState : Bool
  deriving DecidableEq, Repr, Inhabited

namespace Ceremony

private def textAt (value : Cbor.Value) (key : Cbor.Key) : Except PasskeyError String :=
  match value.textAt key with
  | .error error => .error (.badCose (toString error))
  | .ok text => .ok text

private def bytesAt (value : Cbor.Value) (key : Cbor.Key) : Except PasskeyError ByteArray :=
  match value.bytesAt key with
  | .error error => .error (.badCose (toString error))
  | .ok bytes => .ok bytes

/-- `attStmt` is required to be a map and then ignored. Requiring it keeps a message that is not
an attestation object from being read as one; reading it would mean verifying attestation. -/
private def attestationAuthData (bytes : ByteArray) :
    Except PasskeyError (String × ByteArray) :=
  match Cbor.decode bytes with
  | .error error => .error (.badCose error.name)
  | .ok value => do
    let format ← textAt value fmtKey
    match value.mapAt attStmtKey with
    | .error error => .error (.badCose (toString error))
    | .ok _ => pure (format, ← bytesAt value authDataKey)

/-- The checks both ceremonies share: the authenticator signed over this relying party, and it
reported a gesture. User verification is not required, because whether a tenant demands it is a
policy question and refusing it here would answer that question for every tenant. -/
private def checkAuthData (data : AuthData) (party : RelyingParty) :
    Except PasskeyError Unit :=
  if !Leancrypto.bytesEqual data.rpIdHash (Leancrypto.Sha256.hash party.id.toUTF8) then
    .error .wrongRelyingParty
  else if !data.flags.userPresent then .error .userNotPresent
  else .ok ()

/--
A registration, decided in full.

`attestationObject` and `clientDataJson` are what the browser returned, and `challengeAccepts` is
the ceremony's own test of the challenge the browser echoed.
-/
def verifyRegistration (attestationObject : ByteArray) (clientDataJson : String)
    (challengeAccepts : String → Bool) (party : RelyingParty) :
    Except PasskeyError RegisteredPasskey := do
  let (format, authDataBytes) ← attestationAuthData attestationObject
  let data ← AuthData.parse authDataBytes
  let _ ← checkAuthData data party
  let clientData ← ClientData.parse clientDataJson
  let _ ← clientData.check .registration challengeAccepts party.origins
  match data.attested with
  | none => .error .noAttestedCredential
  | some attested => do
    let (algorithm, publicKey) ← Cose.publicKeyInfo attested.coseKey
    pure
      { passkey := ⟨Leancrypto.Codec.Base64Url.encodeString attested.credentialId⟩
        publicKey
        algorithm
        signCount := data.signCount
        aaguid := attested.aaguid
        backupEligible := data.flags.backupEligible
        backupState := data.flags.backupState
        userVerified := data.flags.userVerified
        format }

/--
Everything about an assertion except the signature, and the bytes the signature is over.

Kept apart from `verifyAssertion` so that every rule an assertion is judged by is decided in a
pure function, leaving only the key operation in `IO`. The signing input is `authenticatorData`
followed by the hash of the client data, which is what the authenticator signed and what nothing
may reassemble differently.
-/
def checkAssertion (authDataBytes : ByteArray) (clientDataJson : String)
    (challengeAccepts : String → Bool) (party : RelyingParty) :
    Except PasskeyError (VerifiedAssertion × ByteArray) := do
  let data ← AuthData.parse authDataBytes
  let _ ← checkAuthData data party
  let clientData ← ClientData.parse clientDataJson
  let _ ← clientData.check .authentication challengeAccepts party.origins
  pure
    ({ signCount := data.signCount
       userVerified := data.flags.userVerified
       backupState := data.flags.backupState },
      authDataBytes ++ Leancrypto.Sha256.hash clientDataJson.toUTF8)

/-- `publicKey` is the `SubjectPublicKeyInfo` stored at registration, and `signature` the DER
`SEQUENCE` the authenticator produced. A key that will not load is held apart from a signature
that will not verify: the first is a stored key that is not a key, the second is the refusal this
whole exercise exists to make. -/
def verifySignature (publicKey signingInput signature : ByteArray) :
    IO (Except PasskeyError Unit) := do
  match ← Libcrypto.Evp.PKey.fromSpki publicKey with
  | none => pure (.error .keyRejected)
  | some key =>
    if ← Libcrypto.Sign.verify (.ecdsa .sha256) key signingInput signature then pure (.ok ())
    else pure (.error .signatureInvalid)

/--
An assertion, signature included.

A convenience over `checkAssertion` and `verifySignature` for a caller driving one ceremony
directly rather than through the service.
-/
def verifyAssertion (authDataBytes : ByteArray) (clientDataJson : String)
    (challengeAccepts : String → Bool) (party : RelyingParty) (publicKey signature : ByteArray) :
    IO (Except PasskeyError VerifiedAssertion) := do
  match checkAssertion authDataBytes clientDataJson challengeAccepts party with
  | .error error => pure (.error error)
  | .ok (verified, signingInput) =>
    match ← verifySignature publicKey signingInput signature with
    | .error error => pure (.error error)
    | .ok () => pure (.ok verified)

end Ceremony

/-- The one operation a passkey needs a key for, as a port: the service above it is generic in its
monad, as the rest of this library's services are, and loading a key is not. A deployment with its
own provider supplies its own; `Passkey.verifier` is the shipped one. -/
structure Verifier (m : Type → Type) where
  verify : (algorithm : CoseAlgorithm) → (publicKey signingInput signature : ByteArray) →
    m (Except PasskeyError Unit)

/-- ES256 through OpenSSL. The signature goes in as the authenticator produced it, a DER
`SEQUENCE`, which is the encoding OpenSSL reads; the raw `R‖S` conversion JOSE needs is not
wanted here. -/
def verifier : Verifier IO where
  verify algorithm publicKey signingInput signature :=
    if algorithm.value != Cose.es256Algorithm then
      pure (.error (.unsupportedAlgorithm algorithm.value))
    else Ceremony.verifySignature publicKey signingInput signature

end Authentication.Passkey
