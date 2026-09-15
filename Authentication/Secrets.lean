/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Authentication.Digest
public import Authentication.Tenant
public import Leancrypto.Codec.Base64Url

/-!
Secrets a tenant configures, and the seam that turns one into the bytes it stands for
(AUTH-15.7.3).

Nothing here encrypts anything. The types describe what is held and what is being asked for, and
the port is how a deployment answers; the implementation shipped behind it needs a cipher, and so
lives in a target that may link one (AUTH-6.11).
-/

public section

namespace Authentication

/-- Names one of a tenant's configured providers. Not tenant-indexed: two tenants using Google
have configured the same provider, and what differs is the credentials they configured it with. -/
structure ProviderId where
  value : String
  deriving DecidableEq, Repr, Inhabited, Hashable

/-- Which of a provider's secrets is wanted. A provider needing more than one is why this is not
implied by the provider alone. -/
inductive SecretField where
  | clientSecret
  | signingKey
  deriving DecidableEq, Repr, Inhabited

def SecretField.name : SecretField → String
  | .clientSecret => "client-secret"
  | .signingKey => "signing-key"

/-- Every field there is, so whatever has to offer the names can list them. -/
def SecretField.all : List SecretField := [.clientSecret, .signingKey]

/-- The names are part of the text form a deployment writes, so reading one back belongs here
beside the writing rather than in each tool that has to accept one. -/
def SecretField.parse (text : String) : Option SecretField :=
  SecretField.all.find? (fun field => field.name == text)

/-- What is being asked for. The three parts are also what the shipped implementation binds as
associated data, so a ciphertext cannot be lifted from one tenant's row into another's, nor from
one field into another (AUTH-15.7.3.1). -/
structure SecretRef where
  tenant : TenantId
  provider : ProviderId
  field : SecretField
  deriving DecidableEq, Repr

/-- A secret encrypted at rest. The key identifier is stored with it so that rotation has the
overlap window AUTH-15.7.2 gives digests, and the nonce because a nonce is not a secret and
reusing one under a key is what destroys the guarantee. -/
structure SealedSecret where
  keyId : KeyId
  nonce : ByteArray
  ciphertext : ByteArray
  tag : ByteArray
  deriving DecidableEq, Inhabited

/-- How a tenant holds one secret. There is no third variant carrying plaintext, and that is the
whole of AUTH-15.7.3: a deployment that configures nothing gets encryption rather than a warning
it can ignore. -/
inductive StoredSecret where
  | sealed (value : SealedSecret)
  /-- Held somewhere this library cannot see, under a name only the client's own resolver
  understands. -/
  | external (reference : String)
  deriving DecidableEq, Inhabited

/--
The text a stored secret is written down as (AUTH-15.7.3.2). Configuration is usually neither a
Lean literal nor a row in the database the secret protects, and a sealed secret with no written
form is one that cannot be configured at all.

The fields are base64url, whose alphabet holds no `.`, so none of them can be read as two. An
external reference is the remainder of the text rather than a field of its own, which costs
nothing and keeps it legible to whoever sets it. The leading `v1` is what lets a later form
replace this one without either having to guess which it is reading.
-/
def StoredSecret.render : StoredSecret → String
  | .sealed value =>
    let field := Leancrypto.Codec.Base64Url.encodeString
    "v1.s." ++ field value.keyId.value.toUTF8 ++ "." ++ field value.nonce ++ "."
      ++ field value.ciphertext ++ "." ++ field value.tag
  | .external reference => "v1.x." ++ reference

/-- Total, because what it reads is configuration: a mistyped environment variable is a startup
that refuses, not one that panics. -/
def StoredSecret.parse (text : String) : Option StoredSecret :=
  match text.toList with
  | 'v' :: '1' :: '.' :: 'x' :: '.' :: reference => some (.external (String.ofList reference))
  | chars =>
    match (chars.splitOn '.').map String.ofList with
    | ["v1", "s", keyId, nonce, ciphertext, tag] => do
      let keyId ← (Leancrypto.Codec.Base64Url.decodeString keyId).bind String.fromUTF8?
      let nonce ← Leancrypto.Codec.Base64Url.decodeString nonce
      let ciphertext ← Leancrypto.Codec.Base64Url.decodeString ciphertext
      let tag ← Leancrypto.Codec.Base64Url.decodeString tag
      some (.sealed { keyId := ⟨keyId⟩, nonce, ciphertext, tag })
    | _ => none

inductive SecretError where
  /-- Sealed under a key the ring no longer carries, which is a rotation that dropped a key still
  in use rather than anything the caller did. -/
  | unknownKey (keyId : KeyId)
  /-- The tag did not verify: the wrong key, a tampered ciphertext, or the right ciphertext read
  under the wrong `SecretRef`. They are one error on purpose, because telling them apart is a
  service to whoever is doing the tampering. -/
  | undecipherable
  /-- The configured key is not the length its cipher requires. -/
  | keyUnusable
  /-- The random source would not produce a nonce to seal under. -/
  | noNonce (detail : String)
  /-- An external secret and nothing to resolve it with. -/
  | noResolver (reference : String)
  deriving DecidableEq, Repr, Inhabited

/-- Selected at startup from configuration, so a structure rather than a class (AUTH-3.5). -/
structure Secrets (m : Type → Type) where
  resolve : SecretRef → StoredSecret → m (Except SecretError ByteArray)

end Authentication
