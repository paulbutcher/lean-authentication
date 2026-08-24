/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Codec.Base64Url
public import Crypto.Sha256
public import Crypto.Compare

/-!
PKCE, `S256` only (§20.5).

`plain` is the default `code_challenge_method` in OAuth 2.1 and is not implemented here, so a
request that omits the method is refused rather than silently downgraded: a challenge that is
its own verifier protects against nothing an attacker who saw the request cannot do.

The comparison is on the encoded form. Base64url has one spelling per byte string, so
comparing the text the client sent against the text the transform produces accepts exactly the
verifiers whose hash matches, and a challenge that was not canonically encoded matches nothing.
-/

@[expose] public section

namespace Authentication.OAuth.Pkce

/-- `BASE64URL-ENCODE(SHA256(ASCII(code_verifier)))`, which is the whole of `S256`. -/
def challengeOf (verifier : String) : String :=
  Codec.Base64Url.encodeString (Crypto.Sha256.hashUtf8 verifier)

/-- The unreserved characters OAuth 2.1 §7.5.2 permits, and only those. -/
def isVerifierChar (c : Char) : Bool :=
  c.isAlphanum || c == '-' || c == '.' || c == '_' || c == '~'

/-- 43 to 128 characters, which is the range that makes the verifier worth having: shorter is
guessable and longer is refused by servers that took the bound literally. -/
def isVerifier (verifier : String) : Bool :=
  43 ≤ verifier.length && verifier.length ≤ 128 && verifier.all isVerifierChar

/--
Whether the verifier is the one the challenge was derived from.

`Crypto.bytesEqual` rather than `==` because the latter stops at the first differing byte, and
what it would then be reporting is how long a correct prefix a guessed verifier had.
-/
def verify (challenge verifier : String) : Bool :=
  Crypto.bytesEqual (challengeOf verifier).toUTF8 challenge.toUTF8

end Authentication.OAuth.Pkce
