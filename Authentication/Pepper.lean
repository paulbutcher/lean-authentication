/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Authentication.Digest
import Crypto.Hmac

public section

namespace Authentication

/--
A server-side pepper and the identifier of the key it is. Supplied by configuration and never
defaulted (AUTH-14.1.6).
-/
structure Pepper where
  keyId : KeyId
  secret : ByteArray

namespace Pepper

def digest (pepper : Pepper) (value : CredentialValue) : Digest :=
  ⟨pepper.keyId, Crypto.hmac pepper.secret value.encoded.toUTF8⟩

/-- Derives one credential from another. The revealed code is derived from the magic token this
way, so that opening the link always shows the same code without the code ever being stored
(AUTH-5.2.2, AUTH-5.3.4). -/
def derive (pepper : Pepper) (label : String) (source : CredentialValue) : ByteArray :=
  Crypto.hmac pepper.secret (label.toUTF8 ++ source.encoded.toUTF8)

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

end Authentication
