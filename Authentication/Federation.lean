/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Authentication.Account
public import Authentication.Invitation
public import Authentication.Digest
public import Authentication.Secrets
public import Authentication.Time

/-!
Signing in with somebody else's provider, as far as it can be decided without effects (§6).

Nothing here performs the protocol. What the provider said arrives as a `ProviderAssertion`, what
the store found arrives as arguments, and the decision comes back as data, so AUTH-6.7 is a total
function over a handful of cases rather than a path through a request handler.
-/

public section

namespace Authentication

/--
The record `state` is bound to (AUTH-6.2).

`verifier` and `nonce` are held rather than digested, which every other secret in this library is
not. Both have to be given back: the verifier is sent to the provider's token endpoint, and the
nonce is compared against the claim in the ID token (AUTH-6.3). A digest can do neither. They are
secrets at rest and are covered by AUTH-15.7.3 along with the provider credentials beside them.
-/
structure FederationState (tenant : TenantId) where
  id : FederationStateId tenant
  /-- Which provider the callback is resuming. A single registered redirect URI serves every
  tenant (AUTH-6.2), and it serves every provider for the same reason: the callback has only
  `state` to recover its context from. -/
  provider : ProviderId
  stateDigest : Digest
  verifier : String
  nonce : String
  /-- The invitation this sign-in is accepting, if it is one. Carried on the record rather than
  supplied at the callback, so that what an acceptance admits comes from the invitation and from
  nowhere the provider or the browser could have written (AUTH-8.3, AUTH-8.6). -/
  invitation : Option (InvitationId tenant) := none
  /-- Where to land afterwards, still to be checked against the allowlist of AUTH-9.8 when it is
  used. Storing it unchecked is deliberate: the allowlist belongs to the tenant's configuration
  at the moment of the redirect, not to this record. -/
  returnTo : Option String
  createdAt : Timestamp
  expiresAt : Timestamp
  consumedAt : Option Timestamp := none
  deriving DecidableEq, Repr

namespace FederationState

/-- The ceiling AUTH-6.2 puts on a state record, applied where one is minted. -/
def maxLifetime : Duration := Duration.minutes 10

/-- Expiry and single use are enforced on read, so correctness does not depend on a sweeper
having run (AUTH-15.4.3). -/
def usable {tenant : TenantId} (state : FederationState tenant) (now : Timestamp) : Bool :=
  state.consumedAt.isNone && now < state.expiresAt

/-- What a successful callback writes back. The store commits it under compare and set, so two
requests racing with one `state` produce one sign-in (AUTH-6.2). -/
def consumed {tenant : TenantId} (state : FederationState tenant) (now : Timestamp) :
    FederationState tenant :=
  { state with consumedAt := some now }

end FederationState

/-- What a provider said about somebody, once its answer has been validated (AUTH-6.5). -/
structure ProviderAssertion where
  identity : FederatedIdentity
  address : EmailAddress
  /-- Whether the provider marked the address verified, which is the single fact AUTH-6.7 turns
  on. A provider that does not say is not saying yes. -/
  addressVerified : Bool
  deriving DecidableEq, Repr

inductive LinkRefusal where
  /-- The provider asserted an address it has not verified. Linking on one is the classic account
  takeover, and no configuration may permit it (AUTH-6.7). -/
  | addressNotVerified
  deriving DecidableEq, Repr, Inhabited

/-- The operator's name for one, for a log record or a span attribute, as `SignInRefusal.name`
gives the refusals of §7 theirs. -/
def LinkRefusal.name : LinkRefusal → String
  | .addressNotVerified => "address-not-verified"

inductive LinkDecision (tenant : TenantId) where
  /-- This identity is already linked. Nothing is written. -/
  | signIn (account : AccountId tenant)
  /-- The identity is new and belongs to an account that has already proven the address. -/
  | link (account : AccountId tenant)
  /-- Nobody in this tenant holds the address, so the account is the signup policy's to allow
  or refuse (AUTH-6.10). -/
  | create
  | refuse (reason : LinkRefusal)
  deriving DecidableEq, Repr

namespace Federation

/--
Whether an assertion signs somebody in, and as whom (AUTH-6.7).

`linked` is the credential stored for this issuer and subject, and `holder` the account in this
tenant holding the asserted address as one it has itself verified. Both come from the store; this
decides, and writes nothing.

An assertion the provider has not marked verified is refused even when no account holds the
address. AUTH-6.7 settles only the linking half, and §18.11 records the other as open; refusing is
the answer that cannot be the wrong one to have shipped.
-/
def decide {tenant : TenantId} (assertion : ProviderAssertion) (linked : Option (Credential tenant))
    (holder : Option (Account tenant)) : LinkDecision tenant :=
  match linked with
  -- The subject is the key, not the address (AUTH-6.6), so an identity already linked signs in
  -- whatever the provider now says the address is, and whether or not it verified it.
  | some credential => .signIn credential.account
  | none =>
    if !assertion.addressVerified then .refuse .addressNotVerified
    else match holder with
      | some account => .link account.id
      | none => .create

end Federation

end Authentication
