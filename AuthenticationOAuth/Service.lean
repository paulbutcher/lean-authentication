/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Authentication.Pepper
public import Authentication.Port.Clock
public import Authentication.Store
public import AuthenticationOAuth.Config
public import AuthenticationOAuth.Consent
public import AuthenticationOAuth.Port.ClientMetadata
public import AuthenticationOAuth.Registration
public import AuthenticationOAuth.Request
public import AuthenticationOAuth.Store
public import Codec.Base64Url

/-!
The interpreter at the edge (§20.1).

Every decision about whether a code may be spent, what a token may carry and where a response
may be sent is taken by a pure function in `Grant`, `Request` or `Uri`; this module mints
credentials, reads and writes through the two stores, and performs the one fetch the protocol
needs.

Two things are deliberately not here. Nobody is authenticated: the caller passes the session
credential the browser presented and §5 is what put it there. And nothing is rendered: the
consent page is the host's, so `authorize` hands it everything it must show and `conclude` takes
back what the person said.
-/

public section

namespace Authentication.OAuth.Service

open Authentication Codec

/-- The implementations chosen at startup, together with the peppers in force. `store` is the
core port, reached for the browser's session and for consent; a grant is a consent record and
was never going to live anywhere else. -/
structure Ports (m : Type → Type) where
  store : AuthStore m
  oauth : OAuthStore m
  documents : ClientDocuments m
  peppers : PepperRing

private def randomValue {m : Type → Type} [Monad m] [RandomBytes m] (bytes : Nat) :
    m (Except String CredentialValue) := do
  match ← RandomBytes.draw bytes with
  | .error e => pure (.error e)
  | .ok drawn => pure (.ok ⟨Base64Url.encodeString drawn⟩)

/-- Looks a credential up under every pepper still inside its overlap window, so a rotation does
not invalidate every outstanding token (AUTH-15.7.2). -/
private def byCredential {m : Type → Type} [Monad m] {α : Type} (peppers : PepperRing)
    (value : CredentialValue) (lookup : Digest → m (Option α)) : m (Option α) :=
  let rec search : List Digest → m (Option α)
    | [] => pure none
    | digest :: rest => do
      match ← lookup digest with
      | some found => pure (some found)
      | none => search rest
  search (peppers.present value).digests

/-! ## Authorization -/

/-- Where the user agent is to be sent. -/
structure Redirect where
  location : String
  deriving DecidableEq, Repr, Inhabited

/-- Every authorization response carries `iss`, the error responses included, so that a client
talking to several authorisation servers can tell which one answered before it acts on anything
in the response (RFC 9207 §2). -/
def authorizationResponse {tenant : TenantId} (config : OAuthConfig tenant) (target : String)
    (state : Option String) (params : List (String × String)) : Redirect :=
  ⟨Uri.withQuery target
    (params ++ (match state with | some value => [("state", value)] | none => []) ++
      [("iss", config.issuer)])⟩

/-- What a consent page has to show. Everything on it is either the person's own decision to
make or something a specification requires be displayed. -/
structure ConsentPrompt (tenant : TenantId) where
  /-- Handed back to `conclude`. It carries no signature because whoever receives it is this
  process: a host that would tamper with it can call `conclude` with anything it likes anyway,
  and it is the host that decides who may consent to what. What a host has reason to change is
  `resource` or `requestedScopes` rather than anything in here, and `answered` is what carries
  such a change through to the code. -/
  request : AuthorizationRequest
  account : AccountId tenant
  client : Client
  /-- The host of the `client_id` URL, to be displayed beside the name the client gave itself
  (client ID metadata document draft §6.4). `none` for a client that registered dynamically,
  where there is no domain vouching for the name. -/
  clientHost : Option String
  /-- The host of the redirect URI, which MUST be displayed (MCP authorization security
  considerations). -/
  redirectHost : String
  /-- Whether every redirect URI this client registered is a loopback one, which SHOULD carry a
  further warning: no metadata document can establish who is listening on a port of this
  person's own machine. -/
  loopbackOnly : Bool
  resource : ResourceIndicator
  requestedScopes : List Scope
  /-- What this account has already granted this client for this resource, so a page can show
  what is new about the request. -/
  grantedScopes : List Scope

/--
The request the answer was given about.

`resource` and `requestedScopes` are restated above because a page has to display them, and a
host that amends either is amending the request: a page that offers the deployment's own default
scope set where the client named none does exactly that. Taking both back from the fields that
were displayed is what stops a consent recorded about one resource, or about one set of scopes,
from producing a code bound to another.
-/
def ConsentPrompt.answered {tenant : TenantId} (prompt : ConsentPrompt tenant) :
    AuthorizationRequest :=
  { prompt.request with resource := prompt.resource, scopes := prompt.requestedScopes }

/-- What the person said. The scopes are what they approved, which may be fewer than were asked
for and is narrowed to the request either way. -/
inductive ConsentDecision (tenant : TenantId) where
  | granted (prompt : ConsentPrompt tenant) (scopes : List Scope)
  | denied (prompt : ConsentPrompt tenant)

namespace ConsentDecision

@[expose] def prompt {tenant : TenantId} : ConsentDecision tenant → ConsentPrompt tenant
  | .granted value _ | .denied value => value

/--
What the answer amounts to: the scopes to record, or nothing at all.

Approval is narrowed to the request, so a host cannot record a consent to more than was asked
for by passing back a wider set than the page displayed. What survives that narrowing may be
empty, and an approval of nothing is a refusal spelled the other way: it is what the person's
answer meant, it takes the withdrawal path a refusal takes, and it sends the client the
`access_denied` it knows how to act on rather than a credential that reaches nothing.
-/
@[expose] def settled {tenant : TenantId} : ConsentDecision tenant → Option (List Scope)
  | .denied _ => none
  | .granted value approved =>
    let consented := Scope.granted value.requestedScopes approved
    if consented.isEmpty then none else some consented

end ConsentDecision

inductive Outcome (tenant : TenantId) where
  /-- Render a consent page from this and call `conclude` with the answer. -/
  | consent (prompt : ConsentPrompt tenant)
  /-- Send the user agent here. It is a success or an error; either way the client is entitled
  to it, because the redirect URI has been established as this client's. -/
  | respond (redirect : Redirect)
  /-- Nobody is signed in, or the request asked for a fresh authentication. The host runs the
  sign-in flow of §5 and calls `authorize` again with the session it issued. -/
  | authenticate
  /-- The client, or the URI it asked to be sent back to, could not be established. Nothing may
  be sent to it, so the person is told instead (OAuth 2.1 §4.1.2.1). -/
  | refuse (error : ErrorResponse)

private def refuseWith {tenant : TenantId} (error : OAuthError) (description : String) :
    Outcome tenant :=
  .refuse { error, description }

/-- Resolves a `client_id` that is a metadata document URL. Nothing malformed and no failure is
cached, which the draft §5 requires: a client that publishes a broken document and fixes it must
not be refused until a cache entry expires. -/
private def documentClient {m : Type → Type} [Monad m] {tenant : TenantId} (ports : Ports m)
    (config : OAuthConfig tenant) (now : Timestamp) (id : ClientId) (url : String) :
    m (Except ErrorResponse Client) := do
  match ← ports.oauth.cachedDocument tenant id now with
  | some cached => pure (.ok { id, metadata := cached.metadata, origin := .metadataDocument })
  | none =>
    match ← ports.documents.fetch url with
    | .error _ =>
      pure (.error
        { error := .invalidClient
          description := "the client's metadata document could not be fetched" })
    | .ok fetched =>
      if config.clientDocumentMaxBytes < fetched.size then
        pure (.error
          { error := .invalidClient, description := "the client's metadata document is too large" })
      else
        match clientOfDocument id fetched.document with
        | .error _ =>
          pure (.error
            { error := .invalidClient
              description := "the client's metadata document is not a valid registration" })
        | .ok client =>
          let freshness := match fetched.freshFor with
            | none => config.clientDocumentDefaultAge
            | some allowed =>
              if config.clientDocumentMaxAge ≤ allowed then config.clientDocumentMaxAge
              else allowed
          ports.oauth.cacheDocument tenant
            { client := id
              metadata := client.metadata
              fetchedAt := now
              freshUntil := now.advance freshness }
          pure (.ok client)

/--
One flow with two ways of resolving a client, which is the whole of what supporting both
mechanisms costs. Everything downstream of here sees a `Client`.

A URL-shaped identifier that is not a usable metadata document URL is refused rather than looked
for among the dynamic registrations: otherwise whoever can register dynamically chooses what a
URL-shaped identifier means.
-/
private def resolveClient {m : Type → Type} [Monad m] {tenant : TenantId} (ports : Ports m)
    (config : OAuthConfig tenant) (now : Timestamp) (id : ClientId) :
    m (Except ErrorResponse Client) := do
  match id.registration with
  | .rejected =>
    pure (.error
      { error := .invalidClient
        description := "a URL client identifier must be https, have a path, and name a public host" })
  | .metadataDocument url => documentClient ports config now id url
  | .dynamic =>
    match ← ports.oauth.clientById tenant id with
    | none => pure (.error { error := .invalidClient, description := "no such client" })
    | some record =>
      ports.oauth.touchClient tenant id now
      pure (.ok { id, metadata := record.metadata, origin := .dynamic })

/-- The URI the response goes to. It is matched against the registration exactly, except that a
loopback URI may differ in its port: a native client binds an ephemeral one at the moment it
asks, and without this it cannot connect at all (RFC 8252 §7.3). -/
private def resolveRedirect (client : Client) (requested : Option String) :
    Except ErrorResponse String :=
  match requested with
  | some uri =>
    if Uri.permits client.metadata.redirectUris uri then .ok uri
    else
      .error
        { error := .invalidRequest
          description := "the redirect URI is not one this client registered" }
  | none =>
    match client.metadata.redirectUris with
    | [only] => .ok only
    | _ =>
      .error
        { error := .invalidRequest
          description := "redirect_uri is required when the client registered more than one" }

private def issueCode {m : Type → Type} [Monad m] [RandomBytes m] {tenant : TenantId}
    (ports : Ports m) (config : OAuthConfig tenant) (now : Timestamp)
    (request : AuthorizationRequest) (account : AccountId tenant) (consented : List Scope) :
    m (Outcome tenant) := do
  match ← randomValue 12, ← randomValue 32 with
  | .error _, _ | _, .error _ =>
    pure (.respond (authorizationResponse config request.redirectUri request.state
      [("error", OAuthError.serverError.code)]))
  | .ok grant, .ok value =>
    let decision : GrantDecision tenant :=
      { grant := ⟨grant.encoded⟩
        account
        client := request.clientId
        redirectUri := request.redirectUri
        redirectUriGiven := request.redirectUriGiven
        codeChallenge := request.codeChallenge
        resource := request.resource
        requestedScopes := request.scopes
        consentedScopes := consented }
    ports.oauth.createCode tenant
      (decision.code (ports.peppers.current.digest value) now config.authorizationCodeLifetime)
    pure (.respond (authorizationResponse config request.redirectUri request.state
      [("code", value.encoded)]))

private def sessionFor {m : Type → Type} [Monad m] {tenant : TenantId} (ports : Ports m)
    (now : Timestamp) (presented : Option CredentialValue) : m (Option (Session tenant)) :=
  match presented with
  | none => pure none
  | some value => byCredential ports.peppers value (ports.store.sessionByDigest tenant now)

/--
The authorization endpoint.

`session` is whatever session credential the browser presented; the host reads it from its own
cookie and this decides what it means. A request that cannot be satisfied without asking somebody
something comes back as `consent` or `authenticate`, and the host is what asks.
-/
def authorize {m : Type → Type} [Monad m] [Clock m] [RandomBytes m] {tenant : TenantId}
    (ports : Ports m) (config : OAuthConfig tenant) (params : Params)
    (session : Option CredentialValue) : m (Outcome tenant) := do
  let now ← Clock.now
  match Addressing.parse params with
  | .error error =>
    pure (refuseWith error "client_id is required and may be given only once")
  | .ok addressing =>
    match ← resolveClient ports config now addressing.clientId with
    | .error error => pure (.refuse error)
    | .ok client =>
      match resolveRedirect client addressing.redirectUri with
      | .error error => pure (.refuse error)
      | .ok redirectUri =>
        match AuthorizationRequest.parse params addressing redirectUri with
        | .error error =>
          pure (.respond (authorizationResponse config redirectUri addressing.state error.params))
        | .ok request =>
          let silent := request.prompt.contains .silent
          let stale (issued : Timestamp) : Bool :=
            match request.maxAge with
            | none => false
            | some seconds => issued.advance ⟨seconds⟩ ≤ now
          match ← sessionFor ports now session with
          | some live =>
            if request.prompt.contains .login || stale live.createdAt then
              if silent then
                pure (.respond (authorizationResponse config redirectUri request.state
                  [("error", OAuthError.loginRequired.code)]))
              else pure .authenticate
            else
              let account := live.account
              let history ← ports.store.consentHistory tenant account
              let granted := Consent.granted history request.clientId request.resource
              if !request.prompt.contains .consent && Consent.covers request.scopes granted then
                issueCode ports config now request account granted
              else if silent then
                pure (.respond (authorizationResponse config redirectUri request.state
                  [("error", OAuthError.consentRequired.code)]))
              else
                pure (.consent
                  { request
                    account
                    client
                    clientHost := request.clientId.host?
                    redirectHost :=
                      ((Uri.parts? redirectUri).bind
                        (fun parts => (Uri.hostAndPort? parts.authority).map (·.1))).getD redirectUri
                    loopbackOnly :=
                      client.metadata.redirectUris.all fun uri => (Uri.loopback? uri).isSome
                    resource := request.resource
                    requestedScopes := request.scopes
                    grantedScopes := granted })
          | none =>
            if silent then
              pure (.respond (authorizationResponse config redirectUri request.state
                [("error", OAuthError.loginRequired.code)]))
            else pure .authenticate

/--
What the person said, taken back.

A grant is recorded as a consent entry and a refusal that withdraws one is recorded as another
entry, so what the record says was agreed to in June is still what it says in December.
-/
def conclude {m : Type → Type} [Monad m] [Clock m] [RandomBytes m] {tenant : TenantId}
    (ports : Ports m) (config : OAuthConfig tenant) (decision : ConsentDecision tenant) :
    m (Outcome tenant) := do
  let now ← Clock.now
  let prompt := decision.prompt
  let subject := Consent.subject prompt.request.clientId prompt.resource
  match decision.settled with
  | none =>
    let history ← ports.store.consentHistory tenant prompt.account
    if Consent.standing history prompt.request.clientId prompt.resource then
      ports.store.recordConsent tenant
        { account := prompt.account, subject, version := "", act := .withdrawn, recordedAt := now }
      ports.store.appendAudit tenant ⟨now, .anonymous, .consentWithdrawn prompt.account subject⟩
      ports.oauth.revokeGrants tenant now prompt.account prompt.request.clientId prompt.resource
    pure (.respond (authorizationResponse config prompt.request.redirectUri prompt.request.state
      [("error", OAuthError.accessDenied.code)]))
  | some consented =>
    ports.store.recordConsent tenant
      { account := prompt.account
        subject
        version := Scope.render consented
        act := .granted
        recordedAt := now }
    ports.store.appendAudit tenant ⟨now, .anonymous, .consentGranted prompt.account subject⟩
    issueCode ports config now prompt.answered prompt.account consented

/-! ## Tokens -/

structure TokenResponse where
  accessToken : CredentialValue
  /-- Case insensitive per OAuth 2.1 §4.1.4, and spelled the way RFC 6750 spells it. -/
  tokenType : String := "Bearer"
  expiresIn : Nat
  scope : List Scope
  refreshToken : Option CredentialValue := none
  deriving DecidableEq, Repr, Inhabited

/-- `scope` is always present, not only when it differs from what was asked for. A client that
was granted less than it requested has to be told, and one that was granted what it asked for is
not harmed by being told again. -/
def TokenResponse.toJson (response : TokenResponse) : Json :=
  Json.mkObj <|
    [ ("access_token", Json.str response.accessToken.encoded),
      ("token_type", Json.str response.tokenType),
      ("expires_in", Json.ofNat response.expiresIn),
      ("scope", Json.str (Scope.render response.scope)) ]
    ++ (match response.refreshToken with
        | none => []
        | some token => [("refresh_token", Json.str token.encoded)])

private def grantRefused (reason : GrantRejection) : ErrorResponse :=
  match reason with
  | .scopeExceeded =>
    { error := .invalidScope, description := "the requested scope exceeds the grant" }
  | .resourceMismatch =>
    { error := .invalidTarget, description := "the resource is not the one this grant names" }
  | _ => { error := .invalidGrant, description := "the grant is not usable" }

/-- Mints the tokens an entitlement is owed and stores them digested. A refresh token is issued
only where the configuration allows one; RFC 6749 §1.5 leaves that to the server. -/
private def issueTokens {m : Type → Type} [Monad m] [RandomBytes m] {tenant : TenantId}
    (ports : Ports m) (config : OAuthConfig tenant) (now : Timestamp)
    (entitlement : Entitlement tenant) : m (Except ErrorResponse TokenResponse) := do
  -- A credential that permits nothing is not a credential. Refusing it here rather than issuing
  -- it is what lets a client recover: `invalid_grant` sends it back to the authorization
  -- endpoint, where it is asked again, and every other answer leaves it refreshing forever.
  if entitlement.scopes.isEmpty then
    pure (.error { error := .invalidGrant, description := "the grant permits nothing" })
  else
    match ← randomValue 32 with
    | .error _ =>
      pure (.error { error := .serverError, description := "no token could be generated" })
    | .ok accessValue =>
      ports.oauth.createAccessToken tenant
        (entitlement.accessToken (ports.peppers.current.digest accessValue) now
          config.accessTokenLifetime)
      let refresh ← if config.refreshTokensEnabled then
          match ← randomValue 32 with
          | .error _ => pure none
          | .ok refreshValue =>
            ports.oauth.createRefreshToken tenant
              (entitlement.refreshToken (ports.peppers.current.digest refreshValue) now
                config.refreshTokenLifetime)
            pure (some refreshValue)
        else pure none
      pure (.ok
        { accessToken := accessValue
          expiresIn := config.accessTokenLifetime.seconds
          scope := entitlement.scopes
          refreshToken := refresh })

/-- A code presented twice, or two requests racing to spend one, is evidence that somebody other
than the client has it. Everything issued under the grant goes (OAuth 2.1 §4.1.3). -/
private def replayed {m : Type → Type} [Monad m] {tenant : TenantId} (ports : Ports m)
    (now : Timestamp) (grant : GrantId tenant) : m (Except ErrorResponse TokenResponse) := do
  ports.oauth.revokeGrant tenant now grant
  pure (.error
    { error := .invalidGrant, description := "the grant is not usable" })

private def redeemCode {m : Type → Type} [Monad m] [RandomBytes m] {tenant : TenantId}
    (ports : Ports m) (config : OAuthConfig tenant) (now : Timestamp) (request : TokenRequest)
    (presented : String) (redirectUri : Option String) (verifier : String) :
    m (Except ErrorResponse TokenResponse) := do
  match ← byCredential ports.peppers ⟨presented⟩ (ports.oauth.codeByDigest tenant) with
  | none =>
    pure (.error { error := .invalidGrant, description := "the grant is not usable" })
  | some code =>
    match code.bindings request.clientId redirectUri verifier request.resource with
    | .error reason =>
      -- A code presented with the wrong binding is still spent, so that a stolen code cannot be
      -- retried against one guess after another.
      if code.redeemedAt.isSome then replayed ports now code.grant
      else do
        discard (ports.oauth.commitCode tenant code { code with redeemedAt := some now })
        pure (.error (grantRefused reason))
    | .ok () =>
      match code.redeem now with
      | .error .alreadyRedeemed => replayed ports now code.grant
      | .error reason => pure (.error (grantRefused reason))
      | .ok spent =>
        if ← ports.oauth.commitCode tenant code spent then
          issueTokens ports config now code.entitlement
        else replayed ports now code.grant

private def refresh {m : Type → Type} [Monad m] [RandomBytes m] {tenant : TenantId}
    (ports : Ports m) (config : OAuthConfig tenant) (now : Timestamp) (request : TokenRequest)
    (presented : String) (scopes : Option (List Scope)) :
    m (Except ErrorResponse TokenResponse) := do
  match ← byCredential ports.peppers ⟨presented⟩ (ports.oauth.refreshTokenByDigest tenant) with
  | none =>
    pure (.error { error := .invalidGrant, description := "the grant is not usable" })
  | some token =>
    if token.client != request.clientId then
      pure (.error { error := .invalidGrant, description := "the grant is not usable" })
    else
      match token.rotate now with
      | .error .alreadyRedeemed => replayed ports now token.grant
      | .error reason => pure (.error (grantRefused reason))
      | .ok rotated =>
        -- What the refresh is entitled to is settled before the token is spent, so a client
        -- that asked for a scope it was never granted still has the token it presented.
        match token.entitlement scopes request.resource with
        | .error reason => pure (.error (grantRefused reason))
        | .ok entitlement =>
          if ← ports.oauth.commitRefreshToken tenant token rotated then
            issueTokens ports config now entitlement
          else replayed ports now token.grant

/-- The token endpoint. It performs no fetch: a client is identified here by what the code or
the refresh token was bound to, and resolving a metadata document again would let whoever holds
a stolen code make this server issue a request. -/
def token {m : Type → Type} [Monad m] [Clock m] [RandomBytes m] {tenant : TenantId}
    (ports : Ports m) (config : OAuthConfig tenant) (params : Params) :
    m (Except ErrorResponse TokenResponse) := do
  let now ← Clock.now
  match TokenRequest.parse params with
  | .error error => pure (.error error)
  | .ok request =>
    -- A client that only ever refreshes is still a client in use, and pruning goes on nothing
    -- but this. It writes nothing for a metadata document client, which has no row to touch.
    ports.oauth.touchClient tenant request.clientId now
    match request.grant with
    | .authorizationCode code redirectUri verifier =>
      redeemCode ports config now request code redirectUri verifier
    | .refresh presented scopes => refresh ports config now request presented scopes

/-! ## Registration -/

/-- Issues an identifier and stores the metadata. The identifier is base64url, which is not a
URL, so a dynamic registration can never be taken for a metadata document client. -/
def register {m : Type → Type} [Monad m] [Clock m] [RandomBytes m] {tenant : TenantId}
    (ports : Ports m) (body : Json) : m (Except ErrorResponse (ClientRecord tenant)) := do
  let now ← Clock.now
  match ClientMetadata.ofJson body false with
  | .error rejection => pure (.error (Registration.rejection rejection))
  | .ok metadata =>
    match ← randomValue 16 with
    | .error _ =>
      pure (.error { error := .serverError, description := "no client identifier could be generated" })
    | .ok generated =>
      let record : ClientRecord tenant :=
        { id := ⟨generated.encoded⟩, metadata, registeredAt := now, lastUsedAt := now }
      ports.oauth.createClient tenant record
      pure (.ok record)

/-! ## Verification, for a resource server -/

/-- What a valid token says. Identity, the client that holds it, what it is for and what it may
do, and nothing else: the same answer `Service.identify` gives about a session. -/
structure TokenClaims (tenant : TenantId) where
  account : AccountId tenant
  client : ClientId
  grant : GrantId tenant
  resource : ResourceIndicator
  scopes : List Scope
  expiresAt : Timestamp
  deriving DecidableEq, Repr

/--
Whether a presented token may be used here.

`audience` is the resource server's own identifier, and a token issued for anywhere else is
refused however valid it is. That check is the one the MCP specification is emphatic about: a
server that accepts a token issued for somewhere else is the confused deputy of every client
that talks to it.
-/
def verify {m : Type → Type} [Monad m] [Clock m] {tenant : TenantId} (ports : Ports m)
    (presented : CredentialValue) (audience : ResourceIndicator) (required : List Scope := []) :
    m (Except AccessToken.Rejection (TokenClaims tenant)) := do
  let now ← Clock.now
  match ← byCredential ports.peppers presented (ports.oauth.accessTokenByDigest tenant) with
  | none => pure (.error .unknown)
  | some token =>
    match token.admits now audience required with
    | .error rejection => pure (.error rejection)
    | .ok accepted =>
      pure (.ok
        { account := accepted.account
          client := accepted.client
          grant := accepted.grant
          resource := accepted.resource
          scopes := accepted.scopes
          expiresAt := accepted.expiresAt })

/-- The status a rejection is reported with (RFC 6750 §3.1). -/
def rejectionStatus : AccessToken.Rejection → Nat
  | .insufficientScope _ => 403
  | _ => 401

/--
The `WWW-Authenticate` value that goes with a rejection.

Naming the scopes an operation needs is what lets a client come back for them rather than guess,
and all of them are named at once: a challenge that revealed one missing scope at a time would
cost a round trip through the browser for each.

`resourceMetadata` is the resource server's own document, which this library neither serves nor
can guess.
-/
def challenge (rejection : AccessToken.Rejection) (resourceMetadata : Option String := none) :
    String :=
  let quoted := fun (name value : String) => name ++ "=\"" ++ value ++ "\""
  let parts := (match rejection with
      | .unknown => [quoted "error" "invalid_token"]
      | .expired => [quoted "error" "invalid_token", quoted "error_description" "the token has expired"]
      | .revoked => [quoted "error" "invalid_token", quoted "error_description" "the token has been revoked"]
      | .wrongAudience =>
        [quoted "error" "invalid_token", quoted "error_description" "the token is for another resource"]
      | .insufficientScope needed =>
        [quoted "error" "insufficient_scope", quoted "scope" (Scope.render needed)])
    ++ (match resourceMetadata with
        | none => []
        | some uri => [quoted "resource_metadata" uri])
  "Bearer " ++ String.intercalate ", " parts

/-! ## Housekeeping -/

/-- Withdrawing a grant, which is what an account holder's own page calls. The entry that
granted stays where it is and a withdrawal is added beside it; everything issued under the grant
is revoked in the same call, because a consent nobody has and a token that still works is the
worst of both. -/
def revoke {m : Type → Type} [Monad m] [Clock m] {tenant : TenantId} (ports : Ports m)
    (account : AccountId tenant) (client : ClientId) (resource : ResourceIndicator) : m Unit := do
  let now ← Clock.now
  let subject := Consent.subject client resource
  ports.store.recordConsent tenant
    { account, subject, version := "", act := .withdrawn, recordedAt := now }
  ports.store.appendAudit tenant ⟨now, .anonymous, .consentWithdrawn account subject⟩
  ports.oauth.revokeGrants tenant now account client resource

/-- One agent an account has connected: everything a page needs to render a row, and everything
`revoke` needs to act on one. -/
structure Connection (tenant : TenantId) where
  client : ClientId
  /-- What the client called itself. `none` where nothing held here says, which for a metadata
  document client means its document is not in the cache. -/
  clientName : Option String
  /-- Where the name came from. A page that shows one is required to say which of the two
  mechanisms produced it (AUTH-20.6.10), and a page listing what those pages produced owes the
  same. -/
  origin : ClientOrigin
  resource : ResourceIndicator
  /-- Read from the live credential rather than from the consent history. What the row is about
  is what can be done now. -/
  scopes : List Scope
  /-- When the consent behind this was recorded, where the history has one. -/
  since : Option Timestamp
  /-- When the newest credential under the grant was issued or rotated, which is the honest
  answer to whether it is still in use. -/
  lastUsedAt : Timestamp
  deriving DecidableEq, Repr

private def displayName (metadata : ClientMetadata) : Option String :=
  if metadata.clientName.isEmpty then none else some metadata.clientName

/-- What to call a client, from what this server already holds. Nothing is fetched: a listing
that resolved a metadata document would let whoever can name a URL make this server issue a
request, which is the reasoning already recorded on `token`.

A URL-shaped identifier that resolution would refuse reads as a metadata document client with
no name. Nothing can hold a grant under one, so this is a shape rather than a case. -/
private def clientLabel {m : Type → Type} [Monad m] (ports : Ports m) (tenant : TenantId)
    (now : Timestamp) (id : ClientId) : m (Option String × ClientOrigin) := do
  match id.registration with
  | .dynamic =>
    let record ← ports.oauth.clientById tenant id
    pure (record.bind fun record => displayName record.metadata, .dynamic)
  | _ =>
    let cached ← ports.oauth.cachedDocument tenant id now
    pure (cached.bind fun cached => displayName cached.metadata, .metadataDocument)

/--
What this account has connected, one row per client and resource, built from what is live.

A consent entry and a grant are different facts. The history says what somebody agreed to; the
credentials say what can still be done, and a page offering to disconnect an agent is about the
second. The two agree except where a withdrawal has not reached everything, which is a state
`revoke` exists not to produce.

The rows are per client and resource because that is what `revoke` takes. A deployment serving
one resource sees one row per client and need not care.
-/
def connections {m : Type → Type} [Monad m] [Clock m] {tenant : TenantId} (ports : Ports m)
    (account : AccountId tenant) : m (List (Connection tenant)) := do
  let now ← Clock.now
  let live ← ports.oauth.grantsForAccount tenant account now
  let history ← ports.store.consentHistory tenant account
  live.mapM fun summary => do
    let (clientName, origin) ← clientLabel ports tenant now summary.client
    let subject := Consent.subject summary.client summary.resource
    let since :=
      match Authentication.Consent.latest history subject with
      | some entry => if entry.act == .granted then some entry.recordedAt else none
      | none => none
    pure
      { client := summary.client
        clientName
        origin
        resource := summary.resource
        scopes := summary.scopes
        since
        lastUsedAt := summary.lastIssuedAt }

/-- What this account has granted, as scopes, per client and resource. A different question from
`connections`: this is what was agreed to, which outlives the credentials agreeing to it
produced, and a privacy page wants both. -/
def grants {m : Type → Type} [Monad m] {tenant : TenantId} (ports : Ports m)
    (account : AccountId tenant) : m (List ConsentState) :=
  Authentication.Consent.state <$> ports.store.consentHistory tenant account

/-- Dynamic registrations accumulate, one per fresh connection from some clients, and nothing
about the protocol bounds how many. A client runs this from whatever it already uses to run
periodic work. -/
def pruneClients {m : Type → Type} [Monad m] [Clock m] {tenant : TenantId} (ports : Ports m)
    (idle : Duration := Duration.days 30) : m Nat := do
  let now ← Clock.now
  ports.oauth.pruneClients tenant ⟨now.epochSeconds - idle.seconds⟩

/-- Removes the codes, tokens and cached documents nothing can reach. Everything it removes is
already refused on read, so no correctness depends on it having run. -/
def purgeExpired {m : Type → Type} [Monad m] [Clock m] {tenant : TenantId} (ports : Ports m)
    (grace : Duration := Duration.days 1) : m SweepCounts := do
  let now ← Clock.now
  ports.oauth.purgeExpired tenant ⟨now.epochSeconds - grace.seconds⟩

end Authentication.OAuth.Service
