/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import AuthenticationPasskey.Error
public import Authentication
public import Cbor
public import Leancrypto.Der.PublicKey

/-!
A COSE_Key as an authenticator produces it, turned into the `SubjectPublicKeyInfo` a verifier
loads.

The conversion happens once, at registration, and the result is what is stored, so signing in
afterwards decodes no CBOR and reads no COSE labels.
-/

public section

namespace Authentication.Passkey.Cose

/-! The labels this reads. A negative label is key-type specific and a positive one is not, which
is why `-1` means the curve on an EC2 key and the modulus on an RSA one. -/

def ktyLabel : Cbor.Key := .ofInt 1
def algLabel : Cbor.Key := .ofInt 3
def crvLabel : Cbor.Key := .ofInt (-1)
def xLabel : Cbor.Key := .ofInt (-2)
def yLabel : Cbor.Key := .ofInt (-3)

/-- `2` is EC2, the two-coordinate elliptic curve key type. -/
def ec2KeyType : Int := 2

/-- `1` is P-256 among COSE's curves and `-7` is ES256 among its algorithms. The pair is what
every platform authenticator produces, and what WebAuthn requires a relying party to offer. -/
def p256Curve : Int := 1
def es256Algorithm : Int := -7

/-- Each P-256 coordinate is this wide. A shorter one would build a point DER accepts and OpenSSL
rejects; a longer one would shift the other coordinate without changing the length. -/
def coordinateWidth : Nat := 32

/-- An uncompressed point is `0x04 || X || Y`. The prefix is added here because COSE carries the
coordinates apart and DER wants them joined. -/
private def uncompressedPoint (x y : ByteArray) : ByteArray :=
  (ByteArray.mk #[4] ++ x) ++ y

private def coordinate (key : Cbor.Value) (label : Cbor.Key) : Except PasskeyError ByteArray :=
  match key.bytesAt label with
  | .error error => .error (.badCose (toString error))
  | .ok bytes =>
    if bytes.size == coordinateWidth then .ok bytes
    else .error (.badCose "coordinate width")

private def integerAt (key : Cbor.Value) (label : Cbor.Key) : Except PasskeyError Int :=
  match key.intAt label with
  | .error error => .error (.badCose (toString error))
  | .ok value => .ok value

/--
The key and the algorithm it signs under.

Only ES256 is read. Every other algorithm is refused by its identifier rather than attempted,
because a key loaded under the wrong assumption about its shape verifies or fails for reasons
nothing here could explain.
-/
def publicKeyInfo (key : Cbor.Value) : Except PasskeyError (CoseAlgorithm × ByteArray) := do
  let algorithm ← integerAt key algLabel
  if algorithm != es256Algorithm then .error (.unsupportedAlgorithm algorithm)
  else do
    let keyType ← integerAt key ktyLabel
    if keyType != ec2KeyType then .error (.badCose "key type")
    else do
      let curve ← integerAt key crvLabel
      if curve != p256Curve then .error (.badCose "curve")
      else do
        let x ← coordinate key xLabel
        let y ← coordinate key yLabel
        pure (⟨algorithm⟩,
          Leancrypto.Der.ecPublicKeyInfo Leancrypto.Der.prime256v1Oid (uncompressedPoint x y))

end Authentication.Passkey.Cose
