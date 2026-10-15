/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import AuthenticationPasskey.Error
public import Cbor

/-!
`authenticatorData`, the one part of a WebAuthn message that is not CBOR or JSON but a fixed
binary layout: a hash, a flags byte, a counter, and then whatever the flags say follows.

It is read exhaustively rather than up to the field wanted, so that bytes nobody understood
cannot ride along inside something a signature covers.
-/

public section

namespace Authentication.Passkey

/-- The flags byte, read out by name. Each is a single bit, and the two backup bits are what say
whether a credential can outlive the device holding it. -/
structure Flags where
  userPresent : Bool
  userVerified : Bool
  backupEligible : Bool
  backupState : Bool
  attestedCredentialData : Bool
  extensionData : Bool
  deriving DecidableEq, Repr, Inhabited

def Flags.ofByte (byte : UInt8) : Flags :=
  { userPresent := byte &&& 0x01 != 0
    userVerified := byte &&& 0x04 != 0
    backupEligible := byte &&& 0x08 != 0
    backupState := byte &&& 0x10 != 0
    attestedCredentialData := byte &&& 0x40 != 0
    extensionData := byte &&& 0x80 != 0 }

/-- What a registration's `authenticatorData` carries and an assertion's does not. -/
structure AttestedCredential where
  aaguid : ByteArray
  /-- The handle as the authenticator produced it. It is encoded where it is stored, not here. -/
  credentialId : ByteArray
  /-- Left as a decoded CBOR value rather than converted, so that reading the key and reading the
  layout around it are separate failures. -/
  coseKey : Cbor.Value

structure AuthData where
  rpIdHash : ByteArray
  flags : Flags
  signCount : UInt32
  attested : Option AttestedCredential
  extensions : Option Cbor.Value

namespace AuthData

private def byteAt (bytes : ByteArray) (index : Nat) : Except PasskeyError UInt8 :=
  match bytes[index]? with
  | some byte => .ok byte
  | none => .error .truncatedAuthData

/-- `ByteArray.extract` clamps rather than failing, so the length is checked here: a short input
would otherwise yield a shorter field and be read as though it were whole. -/
private def slice (bytes : ByteArray) (start count : Nat) : Except PasskeyError ByteArray :=
  if start + count ≤ bytes.size then .ok (bytes.extract start (start + count))
  else .error .truncatedAuthData

private def bigEndian (bytes : ByteArray) (start count : Nat) : Except PasskeyError Nat := do
  let mut value := 0
  for offset in [0:count] do
    value := value * 256 + (← byteAt bytes (start + offset)).toNat
  pure value

private def readCbor (bytes : ByteArray) (offset : Nat) :
    Except PasskeyError (Cbor.Value × Nat) :=
  match Cbor.decodePrefix bytes offset with
  | .error error => .error (.badCose error.name)
  | .ok result => .ok result

/--
The whole of `authenticatorData`.

The credential id's length is read from the two bytes the layout puts it in and the key is decoded
from where that ends, which is why the key cannot be found without reading everything before it.
Nothing may follow what the flags account for.
-/
def parse (bytes : ByteArray) : Except PasskeyError AuthData := do
  let rpIdHash ← slice bytes 0 32
  let flags := Flags.ofByte (← byteAt bytes 32)
  let signCount ← bigEndian bytes 33 4
  let (attested, afterAttested) ←
    if flags.attestedCredentialData then do
      let aaguid ← slice bytes 37 16
      let length ← bigEndian bytes 53 2
      let credentialId ← slice bytes 55 length
      let (coseKey, next) ← readCbor bytes (55 + length)
      pure (some { aaguid, credentialId, coseKey }, next)
    else pure (none, 37)
  let (extensions, afterExtensions) ←
    if flags.extensionData then do
      let (value, next) ← readCbor bytes afterAttested
      pure (some value, next)
    else pure (none, afterAttested)
  if afterExtensions != bytes.size then .error .trailingAuthData
  pure { rpIdHash, flags, signCount := UInt32.ofNat signCount, attested, extensions }

end AuthData

end Authentication.Passkey
