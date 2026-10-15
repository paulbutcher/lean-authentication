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

/-- Where the relying party's identity is checked from. The id is the registrable domain a
credential is bound to; the origins are what a browser may report having run the ceremony on, and
they are a list because one tenant may answer on more than one. -/
structure RelyingParty where
  id : String
  origins : List String
  deriving DecidableEq, Repr, Inhabited

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

`attestationObject` and `clientDataJson` are what the browser returned, and `challenge` the value
the ceremony was minted with, encoded as it was sent to the page.
-/
def verifyRegistration (attestationObject : ByteArray) (clientDataJson challenge : String)
    (party : RelyingParty) : Except PasskeyError RegisteredPasskey := do
  let (format, authDataBytes) ← attestationAuthData attestationObject
  let data ← AuthData.parse authDataBytes
  let _ ← checkAuthData data party
  let clientData ← ClientData.parse clientDataJson
  let _ ← clientData.check .registration challenge party.origins
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
def checkAssertion (authDataBytes : ByteArray) (clientDataJson challenge : String)
    (party : RelyingParty) : Except PasskeyError (VerifiedAssertion × ByteArray) := do
  let data ← AuthData.parse authDataBytes
  let _ ← checkAuthData data party
  let clientData ← ClientData.parse clientDataJson
  let _ ← clientData.check .authentication challenge party.origins
  pure
    ({ signCount := data.signCount
       userVerified := data.flags.userVerified
       backupState := data.flags.backupState },
      authDataBytes ++ Leancrypto.Sha256.hash clientDataJson.toUTF8)

/--
An assertion, signature included.

`publicKey` is the `SubjectPublicKeyInfo` stored at registration, and `signature` the DER
`SEQUENCE` the authenticator produced, which is the encoding OpenSSL reads without conversion.
-/
def verifyAssertion (authDataBytes : ByteArray) (clientDataJson challenge : String)
    (party : RelyingParty) (publicKey signature : ByteArray) :
    IO (Except PasskeyError VerifiedAssertion) := do
  match checkAssertion authDataBytes clientDataJson challenge party with
  | .error error => pure (.error error)
  | .ok (verified, signingInput) =>
    match ← Libcrypto.Evp.PKey.fromSpki publicKey with
    | none => pure (.error .keyRejected)
    | some key =>
      if ← Libcrypto.Sign.verify (.ecdsa .sha256) key signingInput signature then
        pure (.ok verified)
      else pure (.error .signatureInvalid)

end Ceremony

end Authentication.Passkey
