/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import AuthenticationPasskey

/-!
The WebAuthn ceremonies, against a key OpenSSL generated and a signature OpenSSL produced.

No authenticator is involved, so what this cannot establish is that a real one lays its bytes out
the way this reads them; `KNOWN_ISSUES.md` records that, and the vectors that would settle it are
Phase 6's. What it does establish is the half this repository can be wrong about on its own: the
layout it builds, the DER it writes, and the signing input it reassembles.
-/

namespace Tests.PasskeyCeremony
open Authentication Authentication.Passkey

private def rpId : String := "example.com"

private def party : RelyingParty :=
  { id := rpId, origins := ["https://example.com"] }

private def challenge : String := "Y2hhbGxlbmdlLXZhbHVl"

private def clientDataFor (type origin : String) (challenge : String) : String :=
  "{\"type\":\"" ++ type ++ "\",\"challenge\":\"" ++ challenge
    ++ "\",\"origin\":\"" ++ origin ++ "\",\"crossOrigin\":false}"

private def assertionClientData : String :=
  clientDataFor assertionType "https://example.com" challenge

/-- `authenticatorData` for an assertion: the hash of the relying party id, the flags, and the
counter. Built rather than transcribed, so the test fails if the layout the parser reads and the
layout written here disagree about where a field is. -/
private def assertionAuthData (flags : UInt8) (signCount : UInt32) : ByteArray :=
  (Leancrypto.Sha256.hash rpId.toUTF8).push flags
    ++ ⟨#[(signCount >>> 24).toUInt8, (signCount >>> 16).toUInt8,
          (signCount >>> 8).toUInt8, signCount.toUInt8]⟩

/-- The uncompressed point out of a P-256 `SubjectPublicKeyInfo`, which ends with
`0x04 || X || Y`. Taken by position rather than parsed: the coordinates are wanted only to build a
COSE key from a real one, and reading DER back is not what is under test. -/
private def coordinatesOf (spki : ByteArray) : ByteArray × ByteArray :=
  (spki.extract (spki.size - 64) (spki.size - 32), spki.extract (spki.size - 32) spki.size)

private def coseKeyOf (x y : ByteArray) : Cbor.Value :=
  (Cbor.Value.map?
      [ (Cose.ktyLabel, Cbor.Value.int Cose.ec2KeyType),
        (Cose.algLabel, Cbor.Value.int Cose.es256Algorithm),
        (Cose.crvLabel, Cbor.Value.int Cose.p256Curve),
        (Cose.xLabel, (Cbor.Value.bytes? x).getD .null),
        (Cose.yLabel, (Cbor.Value.bytes? y).getD .null) ]).getD .null

private def flagsUserPresent : UInt8 := 0x01

def checks : IO (List (String × Bool)) := do
  let accepts := fun (echoed : String) => echoed == challenge
  let key ← Libcrypto.Evp.PKey.generate "EC" #[⟨"group", .utf8 "P-256"⟩]
  let spki ← key.toSpki
  let (x, y) := coordinatesOf spki

  -- The DER this library writes for a key is the DER OpenSSL writes for the same key.
  let built := Cose.publicKeyInfo (coseKeyOf x y)
  let builtMatches := match built with
    | .ok (algorithm, info) => algorithm == ⟨Cose.es256Algorithm⟩ && info == spki
    | .error _ => false

  let authData := assertionAuthData flagsUserPresent 7
  let signingInput := authData ++ Leancrypto.Sha256.hash assertionClientData.toUTF8
  let signature ← Libcrypto.Sign.sign (.ecdsa .sha256) key signingInput

  let accepted ← Ceremony.verifyAssertion authData assertionClientData accepts party
    spki signature
  -- The same assertion against a counter the authenticator did not report, which changes the
  -- signing input and must not verify.
  let tampered ← Ceremony.verifyAssertion (assertionAuthData flagsUserPresent 8)
    assertionClientData accepts party spki signature
  let wrongChallenge ← Ceremony.verifyAssertion authData assertionClientData (· == "other") party
    spki signature
  let wrongOrigin ← Ceremony.verifyAssertion authData
    (clientDataFor assertionType "https://attacker.test" challenge) accepts party spki signature
  let wrongCeremony ← Ceremony.verifyAssertion authData
    (clientDataFor registrationType "https://example.com" challenge) accepts party spki signature
  let wrongParty ← Ceremony.verifyAssertion authData assertionClientData accepts
    { party with id := "other.test" } spki signature
  let noGesture ← Ceremony.verifyAssertion (assertionAuthData 0 7) assertionClientData accepts
    party spki signature

  let refusedAs (expected : PasskeyError) (result : Except PasskeyError VerifiedAssertion) : Bool :=
    match result with
    | .error actual => actual == expected
    | .ok _ => false

  pure
    [ ("passkey: the SubjectPublicKeyInfo built from a COSE key is the one OpenSSL writes",
        builtMatches),
      ("passkey: an assertion signed by the registered key verifies",
        match accepted with
        | .ok verified => verified.signCount == 7 && !verified.userVerified
        | .error _ => false),
      ("passkey: changing the counter changes the signing input and the signature fails",
        refusedAs .signatureInvalid tampered),
      ("passkey: a challenge other than the ceremony's is refused",
        refusedAs .challengeMismatch wrongChallenge),
      ("passkey: an origin the tenant does not answer on is refused",
        refusedAs .originNotAllowed wrongOrigin),
      ("passkey: a registration challenge cannot complete an assertion",
        refusedAs .wrongCeremonyType wrongCeremony),
      ("passkey: data signed over another relying party is refused",
        refusedAs .wrongRelyingParty wrongParty),
      ("passkey: an authenticator reporting no gesture is refused",
        refusedAs .userNotPresent noGesture),
      ("passkey: authenticatorData with bytes after the flags account for is refused",
        match AuthData.parse (authData.push 0) with
        | .error .trailingAuthData => true
        | _ => false),
      ("passkey: authenticatorData ending inside a field is refused",
        match AuthData.parse (authData.extract 0 20) with
        | .error .truncatedAuthData => true
        | _ => false),
      ("passkey: an assertion carries no credential to register",
        match AuthData.parse authData with
        | .ok data => data.attested.isNone && data.signCount == 7
        | .error _ => false),
      ("passkey: a COSE key naming an algorithm this library does not verify is refused",
        match Cose.publicKeyInfo (coseKeyOf x (y.extract 0 31)) with
        | .error (.badCose _) => true
        | _ => false),
      ("passkey: client data missing a member it is judged by is refused",
        match ClientData.parse "{\"type\":\"webauthn.get\"}" with
        | .error (.badClientData "challenge") => true
        | _ => false) ]

end Tests.PasskeyCeremony
