/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import AuthenticationOidc.Discovery
public import JoseLibcrypto

/-!
ID token validation (AUTH-6.5) and the claims a sign-in reads off it.

Signature, `iss`, `aud`, `exp` and `iat` are `lean-jose`'s, decided by a `Policy` this file
builds; `nonce` and the address claims are this library's, because neither is a JOSE concern.
-/

public section

namespace Authentication.Oidc

open Leancrypto

/--
The algorithms an ID token may be signed with, decided here and never read from the token or from
what the provider advertises (AUTH-6.5).

Every one is asymmetric. `HS256` is absent and its absence is the point: a verifier that accepts
it will check an RSA-signed token against the provider's public key used as an HMAC secret, and
the public key is public. `EdDSA` is absent because no provider in AUTH-6.9 issues it, and an
algorithm nothing uses is an algorithm nothing has tested.
-/
def signingAlgorithms : Array Jose.Alg :=
  #[.rs256, .rs384, .rs512, .ps256, .ps384, .ps512, .es256, .es384, .es512]

/-- The most clock skew AUTH-6.5 allows. -/
def maxSkew : Std.Time.Second.Offset := 60

/-- What a validated ID token says, reduced to what a sign-in acts on. Everything else the
provider sent is deliberately dropped rather than carried about. -/
structure ProviderAnswer where
  identity : FederatedIdentity
  address : Option EmailAddress
  /-- Whether the provider marked the address verified, which is the single fact AUTH-6.7 turns
  on. A provider that says nothing has not said yes. -/
  addressVerified : Bool
  /-- Google's `hd`, which AUTH-6.9 permits as supporting evidence and never as the domain
  check itself. -/
  hostedDomain : Option String
  deriving Repr

/-- `aud` is the client identifier and `iss` the issuer the document named, both of which are
this tenant's configuration rather than anything the token offered. -/
def policyFor (config : ProviderConfig) (discovery : Discovery) : Option Jose.Policy :=
  Jose.Policy.mk? signingAlgorithms discovery.issuer #[config.clientId] (leeway := maxSkew)

private def boolClaim (claims : Jose.Claims) (name : String) : Bool :=
  match Jose.Read.member? claims.value name with
  | some (.bool value) => value
  -- Some providers send it as a string. `"false"` must not read as present-and-true, so the
  -- comparison is against the affirmative spelling and nothing else.
  | some (.str value) => value == "true"
  | _ => false

private def stringClaim (claims : Jose.Claims) (name : String) : Option String :=
  Jose.Read.stringMember? claims.value name

/--
Everything AUTH-6.5 requires of a token, and then the `nonce` of AUTH-6.3.

The nonce is compared with `bytesEqual` rather than `==`, which stops at the first differing byte
and so reports how long a correct prefix a guess had. It is a value this server minted and the
provider echoed, so the guess is a remote one, but the comparison costs nothing.
-/
def validate (config : ProviderConfig) (discovery : Discovery) (keys : Jose.KeySet Jose.Backend.libcrypto)
    (expectedNonce : String) (token : String) (now : Timestamp) :
    IO (Except OidcError ProviderAnswer) := do
  match policyFor config discovery with
  | none => pure (.error (.badDocument "issuer"))
  | some policy =>
    let moment := Std.Time.Timestamp.ofSecondsSinceUnixEpoch ⟨now.epochSeconds⟩
    match ← Jose.Jwt.verify Jose.Backend.libcrypto policy keys token moment with
    | .error reason => pure (.error (.token reason))
    | .ok claims =>
      match claims.subject with
      | none => pure (.error .subjectMissing)
      | some subject =>
        match stringClaim claims "nonce" with
        | none => pure (.error .nonceMismatch)
        | some presented =>
          if !bytesEqual presented.toUTF8 expectedNonce.toUTF8 then
            pure (.error .nonceMismatch)
          else
            let address := (stringClaim claims "email").bind (EmailAddress.parse · |>.toOption)
            pure (.ok
              { identity := ⟨discovery.issuer, subject⟩
                address
                addressVerified := boolClaim claims "email_verified"
                hostedDomain := stringClaim claims "hd" })

end Authentication.Oidc
