/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Authentication.Crypto.Sha256
import Authentication.Digest

/-!
HMAC-SHA256 (RFC 2104), and the pepper under which credentials are digested (AUTH-5.3.4).
-/

namespace Authentication.Crypto

private def blockSize : Nat := 64

private def blockKey (key : Array UInt8) : Array UInt8 :=
  let shortened := if key.size > blockSize then Sha256.hashArray key else key
  shortened ++ Array.replicate (blockSize - shortened.size) 0

def hmacArray (key message : Array UInt8) : Array UInt8 :=
  let padded := blockKey key
  let inner := padded.map (· ^^^ 0x36)
  let outer := padded.map (· ^^^ 0x5c)
  Sha256.hashArray (outer ++ Sha256.hashArray (inner ++ message))

def hmac (key message : List UInt8) : List UInt8 :=
  (hmacArray key.toArray message.toArray).toList

/--
A server-side pepper and the identifier of the key it is. Supplied by configuration and never
defaulted (AUTH-14.1.6).
-/
structure Pepper where
  keyId : KeyId
  secret : List UInt8

namespace Pepper

def digest (pepper : Pepper) (value : CredentialValue) : Digest :=
  ⟨pepper.keyId, hmac pepper.secret value.encoded.toUTF8.toList⟩

/-- Derives one credential from another. The revealed code is derived from the magic token this
way, so that opening the link always shows the same code without the code ever being stored
(AUTH-5.2.2, AUTH-5.3.4). -/
def derive (pepper : Pepper) (label : String) (source : CredentialValue) : List UInt8 :=
  hmac pepper.secret (label.toUTF8.toList ++ source.encoded.toUTF8.toList)

end Pepper

/--
The peppers a lookup may be satisfied by: the current one, and any still inside its overlap
window. Rotation without this invalidates every outstanding session and invitation at the
moment it happens (AUTH-15.7.2).
-/
structure PepperRing where
  current : Pepper
  retired : List Pepper := []

namespace PepperRing

def keys (ring : PepperRing) : List Pepper := ring.current :: ring.retired

/-- Digests the offered secret under every live key, so a credential stored before a rotation
still matches (AUTH-15.7.2). -/
def present (ring : PepperRing) (value : CredentialValue) : PresentedSecret :=
  ⟨ring.keys.map (·.digest value)⟩

end PepperRing

end Authentication.Crypto
