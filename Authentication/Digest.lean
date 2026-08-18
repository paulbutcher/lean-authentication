/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Codec.Hex
import Crypto.Compare

namespace Authentication

/-- Identifies the pepper that produced a digest, so rotation can keep an overlap window
rather than invalidating every outstanding credential (AUTH-15.7.2). -/
structure KeyId where
  value : String
  deriving DecidableEq, Repr, Inhabited

structure Digest where
  keyId : KeyId
  bytes : ByteArray
  deriving DecidableEq, Inhabited

/-- Shows four bytes and not the rest, so that a digest reaching a log through one of the derived
instances downstream cannot be matched against a stored one (AUTH-14.1.3). -/
instance : Repr Digest where
  reprPrec d _ :=
    Std.Format.text s!"Digest({d.keyId.value}, {Codec.Hex.encodeString (d.bytes.extract 0 4)}...)"

/--
A secret offered by a request, digested under each pepper still inside its overlap window.
The plaintext never reaches the pure layer: digesting needs the pepper, which lives at the
edge, and a credential is never compared in clear.
-/
structure PresentedSecret where
  digests : List Digest
  deriving Repr, Inhabited

/-- Accepts when the digest under the same key matches. A secret offered under a key the stored
digest was not produced with is not a match, however its bytes compare. The comparison is
`Crypto.bytesEqual` and not `==`, because the latter stops at the first differing byte and so
reports how long a correct prefix a guess had (AUTH-5.3.4). -/
def Digest.accepts (stored : Digest) (presented : PresentedSecret) : Bool :=
  match presented.digests.find? (fun d => d.keyId == stored.keyId) with
  | none => false
  | some d => Crypto.bytesEqual d.bytes stored.bytes

/-- The transmitted form of a credential: base64url for tokens, Crockford base32 for codes. -/
structure CredentialValue where
  encoded : String
  deriving DecidableEq, Repr, Inhabited

/--
A freshly generated credential. The value is carried out in an effect, to be put in a mail or a
cookie; only the digest is kept in state, so no stored record can give the credential back
(AUTH-5.3.4).
-/
structure MintedCredential where
  value : CredentialValue
  digest : Digest
  deriving Repr, Inhabited

end Authentication
