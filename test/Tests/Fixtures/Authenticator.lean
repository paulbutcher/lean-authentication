/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import AuthenticationPasskey

/-!
A stand-in for an authenticator: an `authenticatorData` built to the layout, and an attestation
object encoded with `lean-cbor`, over a key the caller generates. What that cannot establish is
that a real device agrees about the layout, which `Tests.PasskeyVectors` does.
-/

namespace Tests.Fixtures.Authenticator
open Authentication Authentication.Passkey

def credentialId : ByteArray := ⟨#[9, 8, 7, 6, 5, 4, 3, 2, 1, 0, 1, 2, 3, 4, 5, 6]⟩

def handle : PasskeyId := ⟨Leancrypto.Codec.Base64Url.encodeString credentialId⟩

def clientDataFor (origin type challenge : String) : String :=
  "{\"type\":\"" ++ type ++ "\",\"challenge\":\"" ++ challenge
    ++ "\",\"origin\":\"" ++ origin ++ "\",\"crossOrigin\":false}"

def coseKeyOf (x y : ByteArray) : ByteArray :=
  ((Cbor.Value.map?
      [ (Cose.ktyLabel, Cbor.Value.int Cose.ec2KeyType),
        (Cose.algLabel, Cbor.Value.int Cose.es256Algorithm),
        (Cose.crvLabel, Cbor.Value.int Cose.p256Curve),
        (Cose.xLabel, (Cbor.Value.bytes? x).getD .null),
        (Cose.yLabel, (Cbor.Value.bytes? y).getD .null) ]).getD .null).encode

/-- `0x41` is user presence and attested credential data; the counter is zero, which is what a
synced passkey reports. -/
def registrationAuthData (rpId : String) (coseKey : ByteArray) : ByteArray :=
  ((((Leancrypto.Sha256.hash rpId.toUTF8).push 0x41 ++ ⟨#[0, 0, 0, 0]⟩)
      ++ ByteArray.mk (Array.replicate 16 0))
      ++ ⟨#[0, UInt8.ofNat credentialId.size]⟩ ++ credentialId) ++ coseKey

def attestationObjectOf (authData : ByteArray) : ByteArray :=
  ((Cbor.Value.map?
      [ (.ofText "fmt", (Cbor.Value.text? "none").getD .null),
        (.ofText "attStmt", (Cbor.Value.map? []).getD .null),
        (.ofText "authData", (Cbor.Value.bytes? authData).getD .null) ]).getD .null).encode

def assertionAuthData (rpId : String) (signCount : UInt32) : ByteArray :=
  (Leancrypto.Sha256.hash rpId.toUTF8).push 0x01
    ++ ⟨#[(signCount >>> 24).toUInt8, (signCount >>> 16).toUInt8,
          (signCount >>> 8).toUInt8, signCount.toUInt8]⟩

def coordinatesOf (spki : ByteArray) : ByteArray × ByteArray :=
  (spki.extract (spki.size - 64) (spki.size - 32), spki.extract (spki.size - 32) spki.size)

/-- A new P-256 key and the attestation object registering it under `rpId`. -/
def generate (rpId : String) : IO (Libcrypto.Evp.PKey × ByteArray) := do
  let key ← Libcrypto.Evp.PKey.generate "EC" #[⟨"group", .utf8 "P-256"⟩]
  let (x, y) := coordinatesOf (← key.toSpki)
  pure (key, attestationObjectOf (registrationAuthData rpId (coseKeyOf x y)))

end Tests.Fixtures.Authenticator
