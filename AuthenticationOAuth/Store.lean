/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import AuthenticationOAuth.Client
public import AuthenticationOAuth.Grant

/-!
The storage port for the authorisation server (§20.15).

The same shape as `AuthStore`, and for the same reasons: it speaks codes, tokens and clients
rather than SQL, every operation takes the tenant, and every identifier it accepts carries the
tenant in its type. Grants themselves are not here; a grant is a consent record and lives in
`AuthStore` where consent already did.

Its contract is not its type signature. Two of the operations below are compare-and-set, and a
backend that implements either as a read followed by a write typechecks and issues two tokens
for one authorization code.
-/

public section

namespace Authentication.OAuth

/-- One grant an account holds, as the credentials issued under it stand.

The scopes are the credential's rather than the consent history's. The history is the authority
on what was agreed to; a credential is the authority on what can be done with it now, and a
listing offered so that somebody can disconnect something is about the second. -/
structure GrantSummary (tenant : TenantId) where
  client : ClientId
  resource : ResourceIndicator
  scopes : List Scope
  /-- When the newest credential under the grant was issued, which is as close as this server
  comes to when the grant was last used: a client still working rotates. -/
  lastIssuedAt : Timestamp
  deriving DecidableEq, Repr

/-- What a sweep removed. -/
structure SweepCounts where
  codes : Nat := 0
  accessTokens : Nat := 0
  refreshTokens : Nat := 0
  documents : Nat := 0
  deriving DecidableEq, Repr, Inhabited

structure OAuthStore (m : Type → Type) where
  /-- A dynamic registration. The identifier is this server's to choose, so there is no
  conflict to report. -/
  createClient : (tenant : TenantId) → ClientRecord tenant → m Unit
  clientById : (tenant : TenantId) → ClientId → m (Option (ClientRecord tenant))
  clients : (tenant : TenantId) → m (List (ClientRecord tenant))
  /-- Records that the registration was used, which is the only thing pruning can go on. Some
  clients register once per fresh connection, and what tells one of those from a client worth
  keeping is whether anybody has authorised it since (AUTH-20.6.7). -/
  touchClient : (tenant : TenantId) → ClientId → Timestamp → m Unit
  /-- Removes the dynamic registrations nobody has used since `unusedSince`, with everything
  issued to them, and reports how many went. Metadata document clients are not touched: there
  is nothing stored for one to accumulate. -/
  pruneClients : (tenant : TenantId) → (unusedSince : Timestamp) → m Nat
  deleteClient : (tenant : TenantId) → ClientId → m Unit
  /-- One document per client, replacing whatever was there. -/
  cacheDocument : (tenant : TenantId) → CachedDocument tenant → m Unit
  /-- `none` once the document is past the freshness the response that carried it allowed, so a
  stale document is not something a caller can forget to check. -/
  cachedDocument : (tenant : TenantId) → ClientId → (now : Timestamp) →
    m (Option (CachedDocument tenant))
  forgetDocument : (tenant : TenantId) → ClientId → m Unit
  createCode : (tenant : TenantId) → AuthorizationCode tenant → m Unit
  codeByDigest : (tenant : TenantId) → Digest → m (Option (AuthorizationCode tenant))
  /-- Compare and set, never read then write. Writes `next` only if the stored code still agrees
  with `expected` about having been redeemed, and reports whether it won. Two requests racing to
  spend one code therefore produce one token response and one `invalid_grant`
  (AUTH-20.10.2). -/
  commitCode : (tenant : TenantId) → (expected next : AuthorizationCode tenant) → m Bool
  createAccessToken : (tenant : TenantId) → AccessToken tenant → m Unit
  /-- Digested, like every other credential this library stores: no record it holds can give a
  token back (AUTH-20.10.6). -/
  accessTokenByDigest : (tenant : TenantId) → Digest → m (Option (AccessToken tenant))
  createRefreshToken : (tenant : TenantId) → RefreshToken tenant → m Unit
  refreshTokenByDigest : (tenant : TenantId) → Digest → m (Option (RefreshToken tenant))
  /-- The same compare and set, on the rotation stamp (AUTH-20.10.4). -/
  commitRefreshToken : (tenant : TenantId) → (expected next : RefreshToken tenant) → m Bool
  /-- Everything issued under one grant, at once. It is one operation because it is what a
  replayed refresh token triggers, and a revocation spread over two calls can be interrupted
  between them. -/
  revokeGrant : (tenant : TenantId) → Timestamp → GrantId tenant → m Unit
  /-- Every grant this account holds for this client and this resource, which is what
  withdrawing the consent has to reach. -/
  revokeGrants : (tenant : TenantId) → Timestamp → AccountId tenant → ClientId →
    ResourceIndicator → m Unit
  /-- Every grant this account holds, live: one entry per client and resource that still has a
  credential under it which has neither expired nor been revoked. A grant whose credentials have
  all lapsed is not listed, because a row nobody can meaningfully revoke is worse than no row.

  `now` is the caller's, as it is wherever else this port needs one: a store reading a clock of
  its own would be a second clock in a system that already has one. -/
  grantsForAccount : (tenant : TenantId) → AccountId tenant → (now : Timestamp) →
    m (List (GrantSummary tenant))
  /-- Removes the codes and tokens nothing can reach and the documents nothing will serve.
  Everything it removes is already refused on read, so no correctness depends on it having run;
  what it bounds is growth. -/
  purgeExpired : (tenant : TenantId) → (before : Timestamp) → m SweepCounts
  /-- The other half of AUTH-4.2.5. `AuthStore.deleteTenant` removes the accounts and the
  consent records; this removes what was issued against them, and a client using both ports
  calls both. -/
  deleteTenant : (tenant : TenantId) → m Unit

end Authentication.OAuth
