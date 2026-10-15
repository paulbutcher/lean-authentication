/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public section

namespace Authentication.Passkey

/--
Why a WebAuthn message was not accepted.

Every case is held apart for the operator rather than for the person asking, who is told the same
thing by whatever renders the refusal. An authenticator that produces a malformed message and one
that signed over the wrong origin are the same failed sign-in and not the same event.
-/
inductive PasskeyError where
  /-- `authenticatorData` ended before a field its flags said was there. -/
  | truncatedAuthData
  /-- Bytes after everything the flags accounted for, which no conforming authenticator emits. -/
  | trailingAuthData
  /-- The attested credential data flag is clear, so a registration has nothing to register. -/
  | noAttestedCredential
  /-- The user presence flag is clear: the authenticator did not report a gesture, so nobody
  consented to this at the device. -/
  | userNotPresent
  /-- The hash the authenticator signed over is not the hash of this relying party's id, which is
  what makes a passkey unusable on any other origin. -/
  | wrongRelyingParty
  /-- `clientDataJSON` was not an object, or the named member was absent or of the wrong type. -/
  | badClientData (field : String)
  /-- `type` named a different ceremony: a challenge issued to register cannot complete an
  assertion, or an authenticator enrolled for one account could be offered as proof of another. -/
  | wrongCeremonyType
  /-- The challenge the browser echoed is not the one this ceremony was minted with. -/
  | challengeMismatch
  /-- The origin the browser reported is not one this tenant answers on. -/
  | originNotAllowed
  /-- The ceremony ran in a cross-origin frame, where the person cannot see whose page they are
  signing in to. -/
  | crossOrigin
  /-- The COSE key or the attestation object did not decode. The reason is `Cbor.Error.name`, so
  a log says which rule of the encoding was broken. -/
  | badCose (reason : String)
  /-- A COSE algorithm this library does not verify. The identifier is carried so that a log says
  which authenticator to go and read about. -/
  | unsupportedAlgorithm (algorithm : Int)
  /-- The key decoded but OpenSSL would not load it, which is a key that is well formed as CBOR
  and not well formed as a key. -/
  | keyRejected
  | signatureInvalid
  deriving DecidableEq, Repr, Inhabited

/-- A short stable string for a log record or a span attribute, as `OidcError.name` gives the
federated refusals theirs. -/
def PasskeyError.name : PasskeyError → String
  | .truncatedAuthData => "truncated-auth-data"
  | .trailingAuthData => "trailing-auth-data"
  | .noAttestedCredential => "no-attested-credential"
  | .userNotPresent => "user-not-present"
  | .wrongRelyingParty => "wrong-relying-party"
  | .badClientData _ => "bad-client-data"
  | .wrongCeremonyType => "wrong-ceremony-type"
  | .challengeMismatch => "challenge-mismatch"
  | .originNotAllowed => "origin-not-allowed"
  | .crossOrigin => "cross-origin"
  | .badCose _ => "bad-cose"
  | .unsupportedAlgorithm _ => "unsupported-algorithm"
  | .keyRejected => "key-rejected"
  | .signatureInvalid => "signature-invalid"

end Authentication.Passkey
