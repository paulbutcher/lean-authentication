/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

namespace Authentication

/-- Identifies the pepper that produced a digest, so rotation can keep an overlap window
rather than invalidating every outstanding credential (AUTH-15.7.2). -/
structure KeyId where
  value : String
  deriving DecidableEq, Repr, Inhabited

structure Digest where
  keyId : KeyId
  bytes : List UInt8
  deriving DecidableEq, Repr, Inhabited

/--
Compares every byte. `==` on lists stops at the first difference, which reports how long a
correct prefix a guess had; that is a usable oracle against a credential compared byte by byte
(AUTH-5.3.4).
-/
def bytesEqual (a b : List UInt8) : Bool :=
  a.length == b.length && (List.zipWith (fun x y => x == y) a b).foldl Bool.and true

/--
A secret offered by a request, digested under each pepper still inside its overlap window.
The plaintext never reaches the pure layer: digesting needs the pepper, which lives at the
edge, and a credential is never compared in clear.
-/
structure PresentedSecret where
  digests : List Digest
  deriving Repr, Inhabited

/-- Accepts when the digest under the same key matches. A secret offered under a key the stored
digest was not produced with is not a match, however its bytes compare. -/
def Digest.accepts (stored : Digest) (presented : PresentedSecret) : Bool :=
  match presented.digests.find? (fun d => d.keyId == stored.keyId) with
  | none => false
  | some d => bytesEqual d.bytes stored.bytes

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
