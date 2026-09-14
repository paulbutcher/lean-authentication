/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import AuthenticationOidc.Keys
public import Std.Http.Data.URI

/-!
The two halves of a federated sign-in: where to send the browser, and what to do when it comes
back (§6).

Neither performs HTTP of its own. Discovery, the key set and the token exchange all arrive as
ports (AUTH-6.12), and what is decided afterwards goes through `Service.issueFor` so that this
route joins the surfaces of §7, §9 and §14.2 rather than growing copies of them (AUTH-14.2.7).
-/

public section

namespace Authentication.Oidc

open Authentication.Service

/-- Exchanging the authorization code. Its own port because the request carries a client secret
and a verifier and returns a token, none of which is a document fetch. -/
structure TokenEndpoint (m : Type → Type) where
  exchange : Discovery → ProviderConfig → (code redirectUri verifier clientSecret : String) →
    m (Except OidcError String)

/-- Validating an ID token. It is a port rather than a call because `lean-jose` verifies in `IO`,
and the decisions above it are worth running in a monad a test chooses (AUTH-6.5, AUTH-6.12). -/
structure IdTokens (m : Type → Type) where
  verify : ProviderConfig → Discovery → (nonce token : String) → Timestamp →
    m (Except OidcError VerifiedIdToken)

/-- The shipped implementation, over a cached key set: at most one refetch for a `kid` the set
lacks, and none at all while the last fetch is recent (AUTH-6.4). -/
def idTokens (keys : ProviderKeys IO) : IdTokens IO where
  verify provider discovery nonce token now := verifyIdToken keys provider discovery nonce token now

/-- The implementations a federated sign-in is wired from. -/
structure SignInPorts (m : Type → Type) where
  metadata : ProviderMetadata m
  idTokens : IdTokens m
  tokens : TokenEndpoint m
  secrets : Secrets m

private def encodeComponent (value : String) : String :=
  toString (Std.Http.URI.EncodedString.encode (r := Std.Http.Internal.Char.isUnreserved) value)

private def query (parameters : List (String × String)) : String :=
  String.intercalate "&"
    (parameters.map fun (name, value) => name ++ "=" ++ encodeComponent value)


/--
The token exchange over a fetcher (AUTH-6.14).

The client secret travels in the body rather than in `Authorization`, which RFC 6749 §2.3.1
permits and every provider in AUTH-6.9 accepts, and which keeps it out of the places a header is
copied to. The response is read for `id_token` alone: an access token from the provider is a
credential for the provider's own API, and this library has no use for one it would then have to
store.
-/
def tokenEndpoint (http : Fetch.Http IO) (limits : Fetch.Limits := {}) : TokenEndpoint IO where
  exchange discovery provider code redirectUri verifier secret := do
    let body := query
      [ ("grant_type", "authorization_code")
      , ("code", code)
      , ("redirect_uri", redirectUri)
      , ("code_verifier", verifier)
      , ("client_id", provider.clientId)
      , ("client_secret", secret) ]
    match ← Fetch.form http limits discovery.tokenEndpoint [("Accept", "application/json")] body with
    | .error reason => pure (.error (.fetch reason))
    | .ok document =>
      match Json.parse document.body with
      | .error _ => pure (.error (.badDocument "json"))
      | .ok value =>
        match (value.getObjVal? "id_token").toOption.bind (·.getStr?.toOption) with
        | some token => pure (.ok token)
        | none => pure (.error (.badDocument "id_token"))

/-- The cookie that binds the state record to the browser that began the flow.

It carries the same value the URL does, and the callback accepts only a `state` that matches it.
Without the pairing anybody holding a `state` and a code could complete the flow in somebody
else's browser, which signs the victim in as the attacker. `Lax` is required rather than an
oversight, for the reason AUTH-5.2.4 gives: the callback is a top-level navigation arriving from
the provider, and `Strict` would withhold the cookie exactly then. -/
def stateCookie (base : BaseUrl) (tenant : TenantId) (value : String) (expiresAt : Timestamp) :
    CookieSpec :=
  { name := "auth_federation"
    value
    path := BaseUrl.tenantPath tenant
    expiresAt
    secure := base.secureCookies
    httpOnly := true
    sameSite := .lax }

structure FederatedStart (tenant : TenantId) where
  authorizationUrl : String
  cookie : CookieSpec
  deriving Repr

private def drawValue {m : Type → Type} [Monad m] [RandomBytes m] (bytes : Nat) :
    m (Option String) := do
  match ← RandomBytes.draw bytes with
  | .error _ => pure none
  | .ok drawn => pure (some (Leancrypto.Codec.Base64Url.encodeString drawn))

/--
Begins a federated sign-in (AUTH-6.1, AUTH-6.2, AUTH-6.3).

Everything secret is minted here and nothing of it is recoverable from what travels: the URL
carries `state`, the challenge and the nonce, and the record holds the verifier and the nonce
against the digest of the state.

The verifier is 43 characters of base64url, which is the shortest RFC 7636 allows and is drawn
from 32 bytes, so it is at the length's floor and the entropy's ceiling at once.
-/
def beginFederated {m : Type → Type} [Monad m] [Clock m] [RandomBytes m] {tenant : TenantId}
    (store : AuthStore m) (peppers : PepperRing) (config : TenantConfig tenant)
    (provider : ProviderConfig) (discovery : Discovery) (redirectUri : String)
    (returnTo : Option String) : m (Option (FederatedStart tenant)) := do
  let now ← Clock.now
  match ← drawValue 16, ← drawValue 32, ← drawValue 16, ← drawValue 12 with
  | some state, some verifier, some nonce, some identifier =>
    let expiresAt := now.advance FederationState.maxLifetime
    store.createFederationState tenant
      { id := ⟨identifier⟩
        provider := provider.id
        stateDigest := peppers.current.digest ⟨state⟩
        verifier
        nonce
        returnTo
        createdAt := now
        expiresAt }
    let url := discovery.authorizationEndpoint ++ "?" ++ query
      [ ("response_type", "code")
      , ("client_id", provider.clientId)
      , ("redirect_uri", redirectUri)
      , ("scope", String.intercalate " " provider.scopes)
      , ("state", state)
      , ("nonce", nonce)
      , ("code_challenge", Pkce.challengeOf verifier)
      , ("code_challenge_method", "S256") ]
    pure (some { authorizationUrl := url, cookie := stateCookie config.baseUrl tenant state expiresAt })
  | _, _, _, _ => pure none

/-- What a completed callback produced: everything `Service.issueFor` returned, and where the
sign-in asked to land. The target is still the tenant's to allow, and `TenantConfig.returnTo`
is what allows it (AUTH-9.8). -/
structure FederatedCompletion (tenant : TenantId) where
  outcome : Outcome tenant
  returnTo : Option String

/--
Completes one (AUTH-6.2, AUTH-6.5, AUTH-6.7).

The order is the order the refusals are cheapest in, and it is also the order that spends nothing
on a request that was never going to work: the cookie pairing first, then the record, then the
single use of it, and only then the exchange that costs an outbound request.
-/
def completeFederated {m : Type → Type} [Monad m] [Clock m] [RandomBytes m] {tenant : TenantId}
    (ports : Ports m) (oidc : SignInPorts m) (config : TenantConfig tenant)
    (provider : ProviderConfig) (discovery : Discovery) (redirectUri : String)
    (presentedState : Option String) (cookie : Option String) (code : String)
    (requester : RequestContext) : m (Except OidcError (FederatedCompletion tenant)) := do
  let now ← Clock.now
  match presentedState, cookie with
  | some presented, some held =>
    if !Leancrypto.bytesEqual presented.toUTF8 held.toUTF8 then pure (.error .nonceMismatch)
    else
      match ← ports.store.federationStateByDigest tenant now (ports.peppers.current.digest ⟨presented⟩) with
      | none => pure (.error .nonceMismatch)
      | some record =>
        -- Single use, under compare and set: two callbacks racing with one `state` produce one
        -- sign-in and one refusal (AUTH-6.2).
        if !(← ports.store.commitFederationState tenant record (record.consumed now)) then
          pure (.error .nonceMismatch)
        else
          match ← oidc.secrets.resolve
              { tenant, provider := provider.id, field := .clientSecret } provider.clientSecret with
          | .error _ => pure (.error (.badDocument "client-secret"))
          | .ok secretBytes =>
            let secret := (String.fromUTF8? secretBytes).getD ""
            match ← oidc.tokens.exchange discovery provider code redirectUri record.verifier secret with
            | .error reason => pure (.error reason)
            | .ok idToken =>
              match ← oidc.idTokens.verify provider discovery record.nonce idToken now with
              | .error reason => pure (.error reason)
              | .ok verified =>
                match verified.address with
                | none => pure (.error (.badDocument "email"))
                | some address =>
                  let subject : SessionSubject tenant :=
                    { origin := .federated verified.identity verified.addressVerified
                      address
                      requester }
                  let outcome ← issueFor ports config subject
                  pure (.ok { outcome, returnTo := record.returnTo })
  | _, _ => pure (.error .nonceMismatch)

end Authentication.Oidc
