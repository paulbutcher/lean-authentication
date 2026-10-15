/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Authentication.Account
public import Authentication.Digest
public import Authentication.Tenant
public import Authentication.Time

/-!
Passkeys as far as they can be decided without effects.

Nothing here parses a WebAuthn message or checks a signature; what an authenticator asserted
arrives as a `PasskeyAssertion` and what the store found arrives as an argument, so the decision
is a total function over a handful of cases rather than a path through a request handler. The
protocol lives in `AuthenticationPasskey`, which is a separate target because verifying a
signature links OpenSSL and the magic link flow must not.
-/

public section

namespace Authentication

/-- Which ceremony a record was minted for. The two are not interchangeable: a challenge issued
to register must not complete an authentication, or a credential enrolled against one account
could be offered as proof of another. -/
inductive PasskeyCeremonyKind where
  | registration
  | authentication
  deriving DecidableEq, Repr, Inhabited

/--
One passkey ceremony in progress, registration or authentication.

Where `FederationState` holds its verifier and nonce in clear because both have to be given back,
every secret here is a digest: the challenge is only ever compared against what the browser echoes
in `clientDataJSON`, and the nonce against what the cookie offers.
-/
structure PasskeyCeremony (tenant : TenantId) where
  id : PasskeyCeremonyId tenant
  kind : PasskeyCeremonyKind
  challenge : Digest
  /-- Binds the browser that began the ceremony, as the attempt cookie's nonce does. The
  challenge already binds the ceremony, but it reaches the page in a response body, where a
  referrer or a log may carry it further; the nonce is never anywhere but the cookie. -/
  bindingNonce : Digest
  /-- The account a registration attaches to, absent on an authentication. Carried on the record
  rather than supplied at completion, so the account comes from the session that began the
  ceremony and from nowhere the browser could write (AUTH-6.7.1 takes the same position). -/
  account : Option (AccountId tenant) := none
  /-- Where to land afterwards, still to be checked against the tenant's allowlist when it is
  used. Stored unchecked deliberately, as `FederationState.returnTo` is. -/
  returnTo : Option String := none
  createdAt : Timestamp
  expiresAt : Timestamp
  consumedAt : Option Timestamp := none
  deriving DecidableEq, Repr

namespace PasskeyCeremony

/-- The ceiling on a ceremony record. A gesture on an authenticator already in the person's hand
needs nothing like the ten minutes a federated round trip is given. -/
def maxLifetime : Duration := Duration.minutes 5

/-- Expiry and single use are enforced on read, so correctness does not depend on a sweeper
having run (AUTH-15.4.3). -/
def usable {tenant : TenantId} (ceremony : PasskeyCeremony tenant) (now : Timestamp) : Bool :=
  ceremony.consumedAt.isNone && now < ceremony.expiresAt

/-- What a completed ceremony writes back. The store commits it under compare and set, so two
requests racing with one challenge produce one sign-in. -/
def consumed {tenant : TenantId} (ceremony : PasskeyCeremony tenant) (now : Timestamp) :
    PasskeyCeremony tenant :=
  { ceremony with consumedAt := some now }

/-- The cookie names the ceremony and carries the nonce it is checked against, so holding a
ceremony id is not enough to be taken for the browser that began it (AUTH-5.2.5 asks the same of
an attempt). -/
def cookieValue {tenant : TenantId} (id : PasskeyCeremonyId tenant) (nonce : CredentialValue) :
    String :=
  id.value ++ ":" ++ nonce.encoded

end PasskeyCeremony

/-- A COSE algorithm identifier, held as the number COSE uses rather than as a name: it is what
the key arrives labelled with, and what selects the means of verification. -/
structure CoseAlgorithm where
  value : Int
  deriving DecidableEq, Repr, Inhabited

/--
What an authenticator reported about a credential it made.

None of it identifies the credential, which is what keeps it beside the credential row rather
than in the descriptor: `CredentialDescriptor.passkey` carries the only field a lookup uses
(AUTH-4.4.2).
-/
structure PasskeyRegistration (tenant : TenantId) where
  /-- The credential these attributes belong to, and the only identifier on the record. The
  passkey id lives on the credential's descriptor and nowhere else, so there is one place it can
  be wrong. -/
  credential : CredentialId tenant
  /-- The key as a `SubjectPublicKeyInfo` rather than as the COSE map it arrived in, so that
  signing in decodes no CBOR at all. -/
  publicKey : ByteArray
  algorithm : CoseAlgorithm
  /-- Zero where the authenticator keeps no counter, which is most of them now that passkeys
  sync between devices. -/
  signCount : UInt32
  transports : List String
  aaguid : ByteArray
  /-- Whether the credential may be backed up, and whether it is. One that is neither lives on a
  single device, which is what decides whether losing that device loses the account. -/
  backupEligible : Bool
  backupState : Bool
  /-- What the person calls it, supplied by the client. An authenticator does not say, and the
  AAGUID names a model rather than a device. -/
  label : String
  createdAt : Timestamp
  -- No `Repr`, unlike the records around it: `ByteArray` has none derived, and a key and an
  -- AAGUID rendered in full would be noise wherever one was printed.
  deriving DecidableEq

/-- What an authenticator asserted, once the signature over it has been checked. -/
structure PasskeyAssertion where
  passkey : PasskeyId
  /-- Who the authenticator says the credential belongs to. A discoverable credential returns
  one; a credential presented against an `allowCredentials` list may not. -/
  userHandle : Option String
  signCount : UInt32
  deriving DecidableEq, Repr

inductive PasskeyRefusal where
  /-- No credential in this tenant carries that passkey id. The same refusal covers a credential
  belonging to another tenant, because the lookup never leaves this one. -/
  | unknownCredential
  /-- The authenticator returned a user handle naming an account other than the one the
  credential belongs to. -/
  | userHandleMismatch
  deriving DecidableEq, Repr, Inhabited

/-- The operator's name for one, for a log record or a span attribute, as `LinkRefusal.name` gives
the refusal of AUTH-6.7 its. -/
def PasskeyRefusal.name : PasskeyRefusal → String
  | .unknownCredential => "unknown-credential"
  | .userHandleMismatch => "user-handle-mismatch"

inductive PasskeyDecision (tenant : TenantId) where
  | signIn (account : AccountId tenant)
  | refuse (reason : PasskeyRefusal)
  deriving DecidableEq, Repr

namespace Passkey

/--
What goes on the authenticator as the user handle: the account's own identifier.

It is already an opaque value drawn at random per account and is never the address, which is what
a handle has to be, given that it is stored on the authenticator in clear and shown in account
pickers. Reusing it rather than minting a second identifier is deliberate: a handle cannot be
changed once an authenticator holds it, so a separate one would be a value that must agree with
the account forever and could drift from it.
-/
def userHandle {tenant : TenantId} (account : AccountId tenant) : String := account.value

/--
Whether a presented counter went backwards, which is what a cloned authenticator would show.

Both sides reporting zero means the authenticator keeps no counter, and neither that nor a first
assertion against a stored zero is a regression. A regression is recorded and does not refuse: a
synced passkey reports zero from several devices, so refusing on one would turn the common case
into a lockout.
-/
def regressed (stored presented : UInt32) : Bool :=
  (stored != 0 || presented != 0) && presented ≤ stored

/--
Whether an assertion signs somebody in, and as whom.

`stored` is the credential the asserted passkey id names, which the caller read from the store;
this decides and writes nothing, as `Federation.decide` does for the federated route. A passkey
never creates an account: authentication carries no address, so there is nothing a signup policy
could be evaluated against.
-/
def decide {tenant : TenantId} (assertion : PasskeyAssertion)
    (stored : Option (Credential tenant)) : PasskeyDecision tenant :=
  match stored with
  | none => .refuse .unknownCredential
  | some credential =>
    -- An authenticator that offers a handle must offer the one the credential was registered
    -- under. One that offers none has said nothing, which is not a mismatch.
    match assertion.userHandle with
    | none => .signIn credential.account
    | some presented =>
      if presented == userHandle credential.account then .signIn credential.account
      else .refuse .userHandleMismatch

end Passkey

end Authentication
