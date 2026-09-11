/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Authentication.Digest
public import Authentication.Tenant

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
  deriving Inhabited

/-- How a tenant holds one secret. There is no third variant carrying plaintext, and that is the
whole of AUTH-15.7.3: a deployment that configures nothing gets encryption rather than a warning
it can ignore. -/
inductive StoredSecret where
  | sealed (value : SealedSecret)
  /-- Held somewhere this library cannot see, under a name only the client's own resolver
  understands. -/
  | external (reference : String)
  deriving Inhabited

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
