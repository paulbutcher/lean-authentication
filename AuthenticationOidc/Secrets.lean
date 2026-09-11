/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Authentication
public import Libcrypto.Aead

/-!
Provider secrets, encrypted at rest (AUTH-15.7.3.1).

This is the implementation AUTH-15.7.3 requires to ship behind the `Secrets` port, and the reason
the port exists in the core target while this does not: it links a cipher, and a consumer taking
only the magic link flow links none of it (AUTH-6.11).
-/

public section

namespace Authentication.Oidc

open Libcrypto

/-- AES-256-GCM: accelerated wherever the processor offers it, and the algorithm a reviewer
expects to find. `Libcrypto.Aead` offers ChaCha20-Poly1305 through the same interface, and
nothing here would change to use it. -/
def algorithm : Aead.Algorithm := .aes256Gcm

/-- Configured and never defaulted, as AUTH-14.1.6 requires of the pepper, and distinct from it:
a pepper authenticates and this encrypts, and they rotate on schedules of their own. -/
structure SealingKey where
  keyId : KeyId
  secret : ByteArray

/-- The keys a secret may be opened under. Rotation keeps the retired key until nothing is still
sealed with it, which is the overlap window AUTH-15.7.2 gives digests. -/
structure SealingRing where
  current : SealingKey
  retired : List SealingKey := []

def SealingRing.keys (ring : SealingRing) : List SealingKey := ring.current :: ring.retired

/-- Four bytes of big-endian length, then the bytes. -/
private def prefixed (part : String) : ByteArray :=
  let bytes := part.toUTF8
  let n := bytes.size
  ByteArray.mk #[(n >>> 24).toUInt8, (n >>> 16).toUInt8, (n >>> 8).toUInt8, n.toUInt8] ++ bytes

/--
What the ciphertext is bound to (AUTH-15.7.3.1).

Each part is length-prefixed rather than joined by a separator, because a separator has to be a
byte the parts cannot contain and these are the client's own strings. Without the prefix a tenant
called `a` with a provider called `b/c` would agree with a tenant called `a/b` and a provider
called `c`, and agreeing is exactly what lets one tenant's ciphertext be read as another's.
-/
def associatedData (ref : SecretRef) : ByteArray :=
  prefixed ref.tenant.value ++ prefixed ref.provider.value ++ prefixed ref.field.name

/-- Seals under a nonce the caller drew. A nonce repeated under one key destroys both the secrecy
and the authentication, so this is offered beside `sealSecret` rather than instead of it, for a caller
that already has a source it trusts. -/
def sealWith (key : SealingKey) (ref : SecretRef) (nonce plaintext : ByteArray) :
    IO (Except SecretError SealedSecret) := do
  if key.secret.size != algorithm.keyLength then return .error .keyUnusable
  if nonce.size != algorithm.nonceLength then return .error .keyUnusable
  let sealed ← Aead.encrypt algorithm key.secret nonce (associatedData ref) plaintext
  pure (.ok { keyId := key.keyId, nonce, ciphertext := sealed.ciphertext, tag := sealed.tag })

/-- Draws the nonce and seals. This is what a client uses to put a secret into its configuration;
nothing on the sign-in path seals anything. -/
def sealSecret [RandomBytes IO] (key : SealingKey) (ref : SecretRef) (plaintext : ByteArray) :
    IO (Except SecretError SealedSecret) := do
  match ← RandomBytes.draw algorithm.nonceLength with
  | .error detail => pure (.error (.noNonce detail))
  | .ok nonce => sealWith key ref nonce plaintext

/-- A tag that does not verify is one error however it failed, because which of the three it was
is a service to whoever is doing the tampering. -/
def openSecret (ring : SealingRing) (ref : SecretRef) (value : SealedSecret) :
    IO (Except SecretError ByteArray) := do
  match ring.keys.find? (fun key => key.keyId == value.keyId) with
  | none => pure (.error (.unknownKey value.keyId))
  | some key =>
    if key.secret.size != algorithm.keyLength then return .error .keyUnusable
    match ← Aead.decrypt algorithm key.secret value.nonce (associatedData ref)
        { ciphertext := value.ciphertext, tag := value.tag } with
    | none => pure (.error .undecipherable)
    | some plaintext => pure (.ok plaintext)

/-- The port, over a ring of sealing keys. An external secret is refused rather than fetched:
this implementation is the encrypting one, and a deployment naming a reference has said its
secrets live somewhere this cannot see (AUTH-15.7.3). -/
def secrets (ring : SealingRing) : Secrets IO where
  resolve ref stored :=
    match stored with
    | .sealed value => openSecret ring ref value
    | .external reference => pure (.error (.noResolver reference))

end Authentication.Oidc
