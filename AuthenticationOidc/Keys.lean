/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import AuthenticationOidc.IdToken

/-!
The provider's keys, cached, and the one refetch an unknown `kid` may provoke (AUTH-6.4).

The ports here speak the protocol and never HTTP (AUTH-6.12), so the rules of AUTH-6.13 stay above
the seam where this library can keep them rather than below it where a client could drop them.
-/

public section

namespace Authentication.Oidc

structure ProviderMetadata (m : Type → Type) where
  discover : ProviderConfig → m (Except OidcError Discovery)

structure ProviderKeys (m : Type → Type) where
  /-- The provider's published key set. `refresh` asks for one that did not come from cache,
  which is what an unknown `kid` provokes and what the implementation rate limits. -/
  jwks : Discovery → (refresh : Bool) → m (Except OidcError String)

structure KeysConfig where
  /-- How long a key set may be held when the response's headers said nothing. A provider that
  publishes no `max-age` has not said to hold it for ever. -/
  defaultFreshness : Duration := Duration.hours 1
  /-- The least time between two refetches. Without it a token carrying a `kid` nobody has seen
  is an outbound request a stranger can ask for as often as they like (AUTH-6.4). -/
  minRefetchInterval : Duration := Duration.minutes 5
  limits : Fetch.Limits := {}

private structure CachedKeys where
  text : String
  fetchedAt : Timestamp
  freshUntil : Timestamp

/-- Keyed by the URI rather than by the provider, because two tenants configuring one provider
publish the same `jwks_uri` and want one cached copy of it. The list is the right shape: a
deployment has as many entries as it has providers. -/
private abbrev CacheState := List (String × CachedKeys)

private def lookup (state : CacheState) (uri : String) : Option CachedKeys :=
  (state.find? (·.1 == uri)).map (·.2)

private def store (state : CacheState) (uri : String) (entry : CachedKeys) : CacheState :=
  (uri, entry) :: state.filter (·.1 != uri)

/--
The metadata port over a fetcher (AUTH-6.14).

The document is read for the issuer it names, which is checked against the one configured before
anything in it is used.
-/
def metadata (http : Fetch.Http IO) (limits : Fetch.Limits := {}) : ProviderMetadata IO where
  discover config := do
    match ← Fetch.document http limits (wellKnownUrl config.issuer) with
    | .error reason => pure (.error (.fetch reason))
    | .ok document => pure (readDiscovery config.issuer document.body)

/--
The keys port, with the cache and the refetch limit of AUTH-6.4.

A refetch asked for sooner than `minRefetchInterval` after the last one is refused rather than
served from cache, because a caller that asked to refresh has already failed against what the
cache holds and would otherwise be told the same thing twice with no way to tell why.
-/
def keys [Clock IO] (http : Fetch.Http IO) (config : KeysConfig := {}) : IO (ProviderKeys IO) := do
  let cache ← IO.mkRef ([] : CacheState)
  let fetchInto (discovery : Discovery) (now : Timestamp) : IO (Except OidcError String) := do
    match ← Fetch.document http config.limits discovery.jwksUri with
    | .error reason => pure (.error (.fetch reason))
    | .ok document =>
      let held := document.freshFor.getD config.defaultFreshness
      cache.modify (store · discovery.jwksUri
        { text := document.body, fetchedAt := now, freshUntil := now.advance held })
      pure (.ok document.body)
  pure
    { jwks discovery refresh := do
        let now ← Clock.now
        let held := lookup (← cache.get) discovery.jwksUri
        match held with
        | some entry =>
          if refresh then
            if now < entry.fetchedAt.advance config.minRefetchInterval then
              pure (.error .refetchThrottled)
            else fetchInto discovery now
          else if now < entry.freshUntil then pure (.ok entry.text)
          else fetchInto discovery now
        | none => fetchInto discovery now }

private def prepare (text : String) : IO (Except OidcError (Jose.KeySet Jose.Backend.libcrypto)) :=
  match Jose.Jwks.parse {} text with
  | .error reason => pure (.error (.token reason))
  | .ok set => do
    match ← Jose.KeySet.ofJwks Jose.Backend.libcrypto set with
    | .error reason => pure (.error (.token reason))
    | .ok prepared => pure (.ok prepared)

/-- Whether this refusal is the one a refetch could answer: the token named a key the cached set
does not hold, which is what a rotation looks like from here. Every other refusal is about the
token rather than about the keys, and refetching would be an outbound request bought with a
forged signature. -/
private def unknownKey : Jose.Error → Bool
  | .noKeyMatched _ => true
  | _ => false

/--
An ID token, verified against the provider's keys, refetching them at most once (AUTH-6.4).

The retry is conditional on the failure being an unknown key and on the cache being old enough to
refetch, so a token signed by nobody costs one verification and no outbound request.
-/
def verifyIdToken (port : ProviderKeys IO) (config : ProviderConfig) (discovery : Discovery)
    (expectedNonce token : String) (now : Timestamp) : IO (Except OidcError VerifiedIdToken) := do
  match ← port.jwks discovery false with
  | .error reason => pure (.error reason)
  | .ok text =>
    match ← prepare text with
    | .error reason => pure (.error reason)
    | .ok keySet =>
      match ← validate config discovery keySet expectedNonce token now with
      | .ok verified => pure (.ok verified)
      | .error first =>
        let retryable := match first with
          | .token reason => unknownKey reason
          | _ => false
        if !retryable then pure (.error first)
        else
          match ← port.jwks discovery true with
          | .error _ => pure (.error first)
          | .ok fresh =>
            match ← prepare fresh with
            | .error _ => pure (.error first)
            | .ok refreshed => validate config discovery refreshed expectedNonce token now

end Authentication.Oidc
