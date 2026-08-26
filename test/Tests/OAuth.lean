/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import AuthenticationOAuth
import AuthenticationSqlite
import AuthenticationPostgres
import Tests.Postgres

/-!
The authorisation server (§20).

The claims that are properties of a pure function are theorems, because each of them is a
security defect rather than a cosmetic one if it is ever false, and because a check that
inspected the output of one exchange would not see it: a code that can be spent twice, a token
whose audience is not what was asked for, or a port-agnostic redirect match that admitted a host
on the internet all look exactly like a working flow from outside.

What has to be driven is everything the theorems do not constrain: that the two ways of
resolving a client reach the same flow, that a replayed code takes its grant with it, and that
what the store wrote is what the next request reads. Those run against the same statements
production runs, in memory and against the reference backend.
-/

namespace Tests.OAuth
open Authentication Authentication.OAuth

/-! ## Theorems -/

private theorem zipWith_self_foldl (l : List UInt8) (b : Bool) :
    (List.zipWith (fun x y => x == y) l l).foldl Bool.and b = b := by
  induction l generalizing b with
  | nil => simp
  | cons x xs ih =>
    simp only [List.zipWith_cons_cons, List.foldl_cons, beq_self_eq_true, Bool.and_true, ih]

/-- Comparing every byte is what makes a verifier check free of an early exit, and an early exit
is what would report how long a correct prefix a guess had. -/
theorem bytesEqual_self (a : ByteArray) : Crypto.bytesEqual a a = true := by
  unfold Crypto.bytesEqual
  simp only [beq_self_eq_true, Bool.true_and, zipWith_self_foldl]

/-- The transform and the comparison agree: whatever the verifier, the challenge derived from it
is the one that accepts it. -/
theorem pkce_accepts_its_own_challenge (verifier : String) :
    Pkce.verify (Pkce.challengeOf verifier) verifier = true := by
  simp only [Pkce.verify]
  exact bytesEqual_self _

/-- The port-agnostic match admits no host that is not a loopback address. Everything else about
a redirect URI is compared as a string, so this is the whole of the exception. -/
theorem loopback_is_loopback {uri : String} {host : Uri.Loopback}
    (h : Uri.loopback? uri = some host) : Uri.loopbackHosts.contains host.host = true := by
  unfold Uri.loopback? at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · split at h
      · simp at h
      · split at h
        · rename_i condition
          simp only [Option.some.injEq] at h
          subst h
          simp only [Bool.and_eq_true] at condition
          exact condition.left
        · simp at h

/-- And it is reached only when both URIs are loopback ones, so no pair of ordinary URIs can
match on anything but the string comparison. -/
theorem matchesIgnoringPort_is_loopback {registered presented : String}
    (h : Uri.matchesIgnoringPort registered presented = true) :
    ∃ r p, Uri.loopback? registered = some r ∧ Uri.loopback? presented = some p
      ∧ Uri.loopbackHosts.contains r.host = true ∧ Uri.loopbackHosts.contains p.host = true := by
  unfold Uri.matchesIgnoringPort at h
  split at h
  · rename_i r p heqr heqp
    exact ⟨r, p, heqr, heqp, loopback_is_loopback heqr, loopback_is_loopback heqp⟩
  · simp at h

/-- An authorization code is redeemed at most once. The store's compare-and-set is conditioned
on the stamp this writes, so what holds of the state here holds of two concurrent requests. -/
theorem code_redeemed_at_most_once {tenant : TenantId} {now later : Timestamp}
    {code next : AuthorizationCode tenant} (h : AuthorizationCode.redeem now code = .ok next) :
    AuthorizationCode.redeem later next = .error .alreadyRedeemed := by
  unfold AuthorizationCode.redeem at h ⊢
  split at h
  · simp at h
  · split at h
    · simp at h
    · simp only [Except.ok.injEq] at h
      subst h
      simp

/-- A rotated refresh token is dead in the same way. -/
theorem refresh_rotated_at_most_once {tenant : TenantId} {now later : Timestamp}
    {token next : RefreshToken tenant} (h : RefreshToken.rotate now token = .ok next) :
    RefreshToken.rotate later next = .error .alreadyRedeemed := by
  unfold RefreshToken.rotate at h ⊢
  split at h
  · simp at h
  · split at h
    · simp at h
    · split at h
      · simp at h
      · simp only [Except.ok.injEq] at h
        subst h
        simp

/-- A token's audience is the `resource` its request named, at every step between the two. -/
theorem code_audience_is_the_named_resource {tenant : TenantId} (decision : GrantDecision tenant)
    (digest : Digest) (now : Timestamp) (lifetime : Duration) :
    (decision.code digest now lifetime).resource = decision.resource := rfl

theorem entitlement_keeps_the_audience {tenant : TenantId} (code : AuthorizationCode tenant) :
    code.entitlement.resource = code.resource := rfl

theorem access_token_audience {tenant : TenantId} (entitlement : Entitlement tenant)
    (digest : Digest) (now : Timestamp) (lifetime : Duration) :
    (entitlement.accessToken digest now lifetime).resource = entitlement.resource := rfl

/-- And it is used for nothing else: a token accepted at an audience is a token issued for it. -/
theorem admits_only_its_own_audience {tenant : TenantId} {token accepted : AccessToken tenant}
    {now : Timestamp} {audience : ResourceIndicator} {required : List Scope}
    (h : token.admits now audience required = .ok accepted) : token.resource = audience := by
  unfold AccessToken.admits at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · split at h
      · simp at h
      · rename_i condition
        simpa using condition

/-- An issued token's scopes are a subset of those consented to. -/
theorem code_scopes_were_consented {tenant : TenantId} (decision : GrantDecision tenant)
    (digest : Digest) (now : Timestamp) (lifetime : Duration) :
    Scope.subset (decision.code digest now lifetime).scopes decision.consentedScopes = true := by
  simp [GrantDecision.code, Scope.subset, Scope.granted, List.all_eq_true]

theorem access_token_scopes {tenant : TenantId} (entitlement : Entitlement tenant)
    (digest : Digest) (now : Timestamp) (lifetime : Duration) :
    (entitlement.accessToken digest now lifetime).scopes = entitlement.scopes := rfl

/-- A consent that is recorded as granted grants something. An approval that narrows away to
nothing takes the refusal path instead, so no entry is ever written whose scopes reach nothing
and which every later request would then read back as a standing consent. -/
theorem settled_grants_something {tenant : TenantId}
    {decision : OAuth.Service.ConsentDecision tenant} {scopes : List Scope}
    (h : decision.settled = some scopes) : scopes.isEmpty = false := by
  unfold OAuth.Service.ConsentDecision.settled at h
  split at h
  · simp at h
  · dsimp only at h
    split at h
    · simp at h
    · rename_i condition
      simp only [Option.some.injEq] at h
      subst h
      simpa using condition

/-- And it grants no more than was asked for: what is recorded is a subset of what the page
displayed, whatever the host passes back. -/
theorem settled_is_within_the_request {tenant : TenantId}
    {decision : OAuth.Service.ConsentDecision tenant} {scopes : List Scope}
    (h : decision.settled = some scopes) :
    Scope.subset scopes decision.prompt.requestedScopes = true := by
  unfold OAuth.Service.ConsentDecision.settled at h
  split at h
  · simp at h
  · dsimp only at h
    split at h
    · simp at h
    · simp only [Option.some.injEq] at h
      subst h
      simp only [OAuth.Service.ConsentDecision.prompt, Scope.subset, Scope.granted,
        List.all_eq_true]
      intro scope member
      simpa using (List.mem_filter.mp member).left

/--
Narrowing twice against the same request narrows no further.

`conclude` records what `settled` returns and issues a code from `ConsentPrompt.answered`, which
narrows it a second time against the scopes the page displayed. This is why the two agree: the
code a person's answer produces carries exactly the scopes the entry written beside it records,
so the consent history is a reading of what was issued rather than an account of it.
-/
theorem granted_narrows_once (requested approved : List Scope) :
    Scope.granted requested (Scope.granted requested approved)
      = Scope.granted requested approved := by
  simp only [Scope.granted]
  apply List.filter_congr
  intro scope member
  simp only [List.contains_eq_mem, List.mem_filter, member, true_and, decide_eq_true_eq]

/-- The strings of a JSON array field, which is what the metadata claims below are about. -/
private def advertised (document : Json) (field : String) : List String :=
  match (document.getObjVal? field).toOption with
  | some (.arr elements) =>
    elements.toList.filterMap fun element =>
      match element with
      | .str value => some value
      | _ => none
  | _ => []

/-- The metadata document always advertises `S256`, whatever the configuration. A client that
does not find `code_challenge_methods_supported` must refuse to proceed, so this is the field
that decides whether this server is usable at all. -/
theorem metadata_advertises_s256 {tenant : TenantId} (config : OAuthConfig tenant) :
    advertised (metadataDocument config) "code_challenge_methods_supported" = ["S256"] := rfl

/-- And it always offers `"none"`, which together with the metadata document flag is what a
client checks before using a URL as its identifier. -/
theorem metadata_offers_public_clients {tenant : TenantId} (config : OAuthConfig tenant) :
    advertised (metadataDocument config) "token_endpoint_auth_methods_supported" = ["none"] := rfl

/-! ## The fakes -/

initialize clockRef : IO.Ref Timestamp ← IO.mkRef ⟨1700000000⟩
initialize drawCounter : IO.Ref Nat ← IO.mkRef 0
initialize fetchCount : IO.Ref Nat ← IO.mkRef 0

instance : Clock IO where
  now := clockRef.get

instance : RandomBytes IO where
  draw count := do
    let index ← drawCounter.modifyGet fun n => (n, n + 1)
    pure (.ok ((Crypto.Sha256.hashUtf8 s!"oauth-seed-{index}").extract 0 count))

def peppers : PepperRing :=
  { current := { keyId := ⟨"pepper-1"⟩, secret := Crypto.Sha256.hashUtf8 "test pepper" } }

private def address (raw : String) : EmailAddress := (EmailAddress.parse raw).toOption.getD default

def clientDocumentUrl : String := "https://app.example.test/oauth/client.json"

def loopbackRedirect : String := "http://127.0.0.1:33418/callback"

def webRedirect : String := "https://app.example.test/callback"

def clientDocument : Json :=
  Json.mkObj
    [ ("client_id", .str clientDocumentUrl),
      ("client_name", .str "Example MCP Client"),
      ("redirect_uris", .arr #[.str loopbackRedirect, .str webRedirect]),
      ("grant_types", .arr #[.str "authorization_code", .str "refresh_token"]),
      ("response_types", .arr #[.str "code"]),
      ("token_endpoint_auth_method", .str "none") ]

/-- The one adapter these tests stand in for. It counts its calls, which is how the cache is
observed: a second authorization request that fetched again would not be caching. -/
def documents : ClientDocuments IO where
  fetch url := do
    fetchCount.modify (· + 1)
    if url == clientDocumentUrl then
      pure (.ok
        { document := clientDocument
          freshFor := some (Duration.minutes 30)
          size := clientDocument.compress.length })
    else pure (.error "no such document")

/-! ## The exchange -/

def resource : String := "https://mcp.example.test/mcp"

/-- Forty-seven unreserved characters, which is inside the range OAuth 2.1 §7.5.2 fixes. -/
def verifier : String := "abcdefghijklmnopqrstuvwxyz0123456789-._~ABCDEFG"

def sessionCredential : CredentialValue := ⟨"a-session-credential"⟩

private def authorizeParams (client redirect scope : String) : Params :=
  [ ("response_type", "code"),
    ("client_id", client),
    ("redirect_uri", redirect),
    ("scope", scope),
    ("state", "opaque-state"),
    ("code_challenge", Pkce.challengeOf verifier),
    ("code_challenge_method", "S256"),
    ("resource", resource) ]

/-- The same request with the resource and the scope parameter both open. `none` omits `scope`
altogether, which is the case that matters, and the resource is open so that a scope test does
not share a consent subject with the flow above it. -/
private def scopeParams (client redirect target : String) (scope : Option String) : Params :=
  [ ("response_type", "code"),
    ("client_id", client),
    ("redirect_uri", redirect),
    ("state", "opaque-state"),
    ("code_challenge", Pkce.challengeOf verifier),
    ("code_challenge_method", "S256"),
    ("resource", target) ]
  ++ (match scope with | none => [] | some value => [("scope", value)])

private def exchangeParamsAt (client code redirect target : String) : Params :=
  [ ("grant_type", "authorization_code"),
    ("client_id", client),
    ("code", code),
    ("redirect_uri", redirect),
    ("code_verifier", verifier),
    ("resource", target) ]

private def exchangeParams (client code redirect : String) : Params :=
  exchangeParamsAt client code redirect resource

/-- Reads one parameter out of a redirect. The values these tests look at are base64url or a
fixed string, so nothing here has to decode. -/
private def queryValue (location name : String) : Option String :=
  let query := String.ofList ((location.toList.dropWhile (· != '?')).drop 1)
  (query.splitOn "&").findSome? fun pair =>
    match pair.splitOn "=" with
    | [key, value] => if key == name then some value else none
    | _ => none

private def location {tenant : TenantId} : OAuth.Service.Outcome tenant → Option String
  | .respond redirect => some redirect.location
  | _ => none

private def prompt? {tenant : TenantId} :
    OAuth.Service.Outcome tenant → Option (OAuth.Service.ConsentPrompt tenant)
  | .consent value => some value
  | _ => none

private def refusal {tenant : TenantId} : OAuth.Service.Outcome tenant → Option OAuthError
  | .refuse error => some error.error
  | _ => none

private def rejected {tenant : TenantId} (expected : AccessToken.Rejection) :
    Except AccessToken.Rejection (OAuth.Service.TokenClaims tenant) → Bool
  | .error actual => actual == expected
  | .ok _ => false

private def tokenError : Except ErrorResponse OAuth.Service.TokenResponse → Option OAuthError
  | .error response => some response.error
  | .ok _ => none

/--
Everything that has to be driven, against whichever backend it is handed.

The tenant is derived from `label` so that a run against a real database does not collide with
an earlier one, and it is emptied first so that it does not collide with itself.
-/
def checks (label : String) (store : AuthStore IO) (oauth : OAuthStore IO) :
    IO (List (String × Bool)) := do
  let tenant : TenantId := ⟨label ++ "-oauth"⟩
  let config : OAuthConfig tenant :=
    OAuthConfig.standard ⟨"https://auth.example.test"⟩ [⟨"files:read"⟩, ⟨"files:write"⟩]
  let ports : OAuth.Service.Ports IO := { store, oauth, documents, peppers }
  oauth.deleteTenant tenant
  store.deleteTenant tenant
  let now ← clockRef.get
  let person := address "person@example.com"
  let account : AccountId tenant := ⟨"account-1"⟩
  discard <| store.createAccount tenant
    { id := account
      identity := person.normalise
      primaryEmail := person
      createdAt := now }
  store.createSession tenant
    { id := ⟨"session-1"⟩
      account
      identifierDigest := peppers.current.digest sessionCredential
      createdAt := now
      lastSeenAt := now
      idleExpiresAt := ⟨now.epochSeconds + 3600⟩
      absoluteExpiresAt := ⟨now.epochSeconds + 86400⟩ }
  let session := some sessionCredential
  let fetchesBefore ← fetchCount.get
  -- A metadata document client, from an authorization request to a usable token.
  let asked ← OAuth.Service.authorize ports config
    (authorizeParams clientDocumentUrl webRedirect "files:read") session
  let firstPrompt := prompt? asked
  let firstGrant ← match firstPrompt with
    | none => pure none
    | some p => location <$> OAuth.Service.conclude ports config (.granted p [⟨"files:read"⟩])
  let firstCode := firstGrant.bind (queryValue · "code")
  let firstTokens : Except ErrorResponse OAuth.Service.TokenResponse ← match firstCode with
    | none => pure (.error { error := .serverError, description := "no code" })
    | some code => OAuth.Service.token ports config (exchangeParams clientDocumentUrl code webRedirect)
  let accessToken := firstTokens.toOption.map (·.accessToken)
  let refreshToken := firstTokens.toOption.bind (·.refreshToken)
  let claims : Except AccessToken.Rejection (OAuth.Service.TokenClaims tenant) ← match accessToken with
    | none => pure (.error .unknown)
    | some token => OAuth.Service.verify ports token ⟨resource⟩ [⟨"files:read"⟩]
  let elsewhere : Except AccessToken.Rejection (OAuth.Service.TokenClaims tenant) ← match accessToken with
    | none => pure (.error .unknown)
    | some token => OAuth.Service.verify ports token ⟨"https://other.example.test/mcp"⟩
  let underscoped : Except AccessToken.Rejection (OAuth.Service.TokenClaims tenant) ← match accessToken with
    | none => pure (.error .unknown)
    | some token => OAuth.Service.verify ports token ⟨resource⟩ [⟨"files:write"⟩]
  -- Asking again for what was already consented to does not ask again.
  let again ← OAuth.Service.authorize ports config
    (authorizeParams clientDocumentUrl webRedirect "files:read") session
  let fetchesAfter ← fetchCount.get
  let secondCode := (location again).bind (queryValue · "code")
  let secondTokens : Except ErrorResponse OAuth.Service.TokenResponse ← match secondCode with
    | none => pure (.error { error := .serverError, description := "no code" })
    | some code => OAuth.Service.token ports config (exchangeParams clientDocumentUrl code webRedirect)
  let replayed : Except ErrorResponse OAuth.Service.TokenResponse ← match secondCode with
    | none => pure (.error { error := .serverError, description := "no code" })
    | some code => OAuth.Service.token ports config (exchangeParams clientDocumentUrl code webRedirect)
  let afterReplay : Except AccessToken.Rejection (OAuth.Service.TokenClaims tenant) ← match secondTokens.toOption.map (·.accessToken) with
    | none => pure (.error .unknown)
    | some token => OAuth.Service.verify ports token ⟨resource⟩
  -- A wrong verifier against a fresh code.
  let third ← OAuth.Service.authorize ports config
    (authorizeParams clientDocumentUrl webRedirect "files:read") session
  let thirdCode := (location third).bind (queryValue · "code")
  let wrongVerifier : Except ErrorResponse OAuth.Service.TokenResponse ← match thirdCode with
    | none => pure (.error { error := .serverError, description := "no code" })
    | some code =>
      OAuth.Service.token ports config
        (((exchangeParams clientDocumentUrl code webRedirect).filter (·.1 != "code_verifier"))
          ++ [("code_verifier", "0123456789012345678901234567890123456789012")])
  -- Rotation, and what presenting a rotated token again costs.
  let refreshParams := fun (token : String) =>
    [ ("grant_type", "refresh_token"), ("client_id", clientDocumentUrl),
      ("refresh_token", token), ("resource", resource) ]
  let refreshed : Except ErrorResponse OAuth.Service.TokenResponse ← match refreshToken with
    | none => pure (.error { error := .serverError, description := "no refresh token" })
    | some token => OAuth.Service.token ports config (refreshParams token.encoded)
  let replayedRefresh : Except ErrorResponse OAuth.Service.TokenResponse ← match refreshToken with
    | none => pure (.error { error := .serverError, description := "no refresh token" })
    | some token => OAuth.Service.token ports config (refreshParams token.encoded)
  let afterRefreshReplay : Except AccessToken.Rejection (OAuth.Service.TokenClaims tenant) ← match refreshed.toOption.map (·.accessToken) with
    | none => pure (.error .unknown)
    | some token => OAuth.Service.verify ports token ⟨resource⟩
  -- A native client that bound a different ephemeral port than the one it registered.
  let ephemeral ← OAuth.Service.authorize ports config
    (authorizeParams clientDocumentUrl "http://127.0.0.1:59999/callback" "files:read") session
  let wrongPath ← OAuth.Service.authorize ports config
    (authorizeParams clientDocumentUrl "http://127.0.0.1:59999/elsewhere" "files:read") session
  let notLoopback ← OAuth.Service.authorize ports config
    (authorizeParams clientDocumentUrl "http://evil.example.test:59999/callback" "files:read")
    session
  -- A dynamically registered client, through the same flow.
  let registration := Json.mkObj
    [ ("client_name", .str "Legacy Client"),
      ("redirect_uris", .arr #[.str "http://localhost:8080/callback"]),
      ("grant_types", .arr #[.str "authorization_code"]),
      ("token_endpoint_auth_method", .str "none") ]
  let registered ← OAuth.Service.register (tenant := tenant) ports registration
  let dynamicId := (registered.toOption.map (·.id.value)).getD ""
  let dynamicAsked ← OAuth.Service.authorize ports config
    (authorizeParams dynamicId "http://localhost:8080/callback" "files:read") session
  let dynamicGrant ← match prompt? dynamicAsked with
    | none => pure none
    | some p => location <$> OAuth.Service.conclude ports config (.granted p [⟨"files:read"⟩])
  let dynamicTokens : Except ErrorResponse OAuth.Service.TokenResponse ← match dynamicGrant.bind (queryValue · "code") with
    | none => pure (.error { error := .serverError, description := "no code" })
    | some code =>
      OAuth.Service.token ports config
        (exchangeParams dynamicId code "http://localhost:8080/callback")
  -- Registrations that were never used again, and a client that never existed.
  let unknown ← OAuth.Service.authorize ports config
    (authorizeParams "not-a-registered-client" webRedirect "files:read") session
  let privateHost ← OAuth.Service.authorize ports config
    (authorizeParams "https://169.254.169.254/client.json" webRedirect "files:read") session
  let noResource ← OAuth.Service.authorize ports config
    ((authorizeParams clientDocumentUrl webRedirect "files:read").filter (·.1 != "resource"))
    session
  let plainChallenge ← OAuth.Service.authorize ports config
    (((authorizeParams clientDocumentUrl webRedirect "files:read").filter
      (·.1 != "code_challenge_method")) ++ [("code_challenge_method", "plain")]) session
  -- A request that names no scope, against two resources this account has decided nothing about
  -- and then one it has.
  let scopeTarget := "https://scoped.example.test/mcp"
  let emptyTarget := "https://empty.example.test/mcp"
  let scopeless ← OAuth.Service.authorize ports config
    (scopeParams clientDocumentUrl webRedirect emptyTarget none) session
  let bothAsked ← OAuth.Service.authorize ports config
    (scopeParams clientDocumentUrl webRedirect scopeTarget (some "files:read files:write")) session
  let bothGranted ← match prompt? bothAsked with
    | none => pure none
    | some p =>
      location <$> OAuth.Service.conclude ports config
        (.granted p [⟨"files:read"⟩, ⟨"files:write"⟩])
  let scopelessAgain ← OAuth.Service.authorize ports config
    (scopeParams clientDocumentUrl webRedirect scopeTarget none) session
  let narrower ← OAuth.Service.authorize ports config
    (scopeParams clientDocumentUrl webRedirect scopeTarget (some "files:read")) session
  -- An approval that narrows away to nothing, against the resource nothing stands granted for,
  -- so that what the history gains is the whole of what the decision wrote.
  let approvedNothing ← match prompt? scopeless with
    | none => pure none
    | some p => location <$> OAuth.Service.conclude ports config (.granted p [])
  let emptySubject := Consent.subject ⟨clientDocumentUrl⟩ ⟨emptyTarget⟩
  let afterApprovingNothing ← store.consentHistory tenant account
  -- The other answer OAuth 2.1 §3.2.2.1 allows a scopeless request: a page that offers the
  -- deployment's own default set amends the prompt, and what is issued is what it displayed.
  let withDefaults ← match prompt? scopeless with
    | none => pure none
    | some p =>
      location <$> OAuth.Service.conclude ports config
        (.granted { p with requestedScopes := [⟨"files:read"⟩] } [⟨"files:read"⟩])
  let defaulted : Except ErrorResponse OAuth.Service.TokenResponse ←
    match withDefaults.bind (queryValue · "code") with
    | none => pure (.error { error := .serverError, description := "no code" })
    | some code =>
      OAuth.Service.token ports config
        (exchangeParamsAt clientDocumentUrl code webRedirect emptyTarget)
  let afterDefaults ← store.consentHistory tenant account
  -- Credentials that permit nothing, which nothing above this can produce any more. They are
  -- built against the store directly because a grant recorded before the refusals above went in
  -- is exactly what outlives them.
  let emptyCodeValue : CredentialValue := ⟨"a-code-that-permits-nothing"⟩
  oauth.createCode tenant
    { grant := ⟨"empty-grant-code"⟩
      digest := peppers.current.digest emptyCodeValue
      account
      client := ⟨clientDocumentUrl⟩
      redirectUri := webRedirect
      redirectUriGiven := true
      codeChallenge := Pkce.challengeOf verifier
      resource := ⟨resource⟩
      scopes := []
      issuedAt := now
      expiresAt := ⟨now.epochSeconds + 300⟩ }
  let emptyCodeTokens ← OAuth.Service.token ports config
    (exchangeParams clientDocumentUrl emptyCodeValue.encoded webRedirect)
  let emptyRefreshValue : CredentialValue := ⟨"a-refresh-token-that-permits-nothing"⟩
  oauth.createRefreshToken tenant
    { grant := ⟨"empty-grant-refresh"⟩
      digest := peppers.current.digest emptyRefreshValue
      account
      client := ⟨clientDocumentUrl⟩
      resource := ⟨resource⟩
      scopes := []
      issuedAt := now
      expiresAt := ⟨now.epochSeconds + 3600⟩ }
  let emptyRefreshTokens ← OAuth.Service.token ports config
    (refreshParams emptyRefreshValue.encoded)
  let pruned ← oauth.pruneClients tenant ⟨now.epochSeconds + 1000⟩
  let prunedClient ← oauth.clientById tenant ⟨dynamicId⟩
  let history ← store.consentHistory tenant account
  let issuer := Uri.encodeComponent config.issuer
  pure
    [ (s!"{label}: a metadata document client reaches a consent page",
        (firstPrompt.map (·.client.metadata.clientName)) == some "Example MCP Client")
    , (s!"{label}: the consent page is told the redirect host it must display",
        (firstPrompt.map (·.redirectHost)) == some "app.example.test")
    , (s!"{label}: the consent page is told what was already granted, which is nothing",
        (firstPrompt.map (·.grantedScopes)) == some [])
    , (s!"{label}: a granted request redirects with a code",
        (firstCode.map (·.isEmpty)) == some false)
    , (s!"{label}: the authorization response carries the state it was given",
        firstGrant.bind (queryValue · "state") == some "opaque-state")
    , (s!"{label}: the authorization response carries iss (RFC 9207)",
        firstGrant.bind (queryValue · "iss") == some issuer)
    , (s!"{label}: the code exchanges for an access token",
        firstTokens.toOption.isSome)
    , (s!"{label}: the token carries only the scope that was consented to",
        (firstTokens.toOption.map (·.scope)) == some [⟨"files:read"⟩])
    , (s!"{label}: a refresh token is issued", refreshToken.isSome)
    , (s!"{label}: the token verifies at the resource it names",
        (claims.toOption.map (·.account.value)) == some "account-1")
    , (s!"{label}: the token is refused at any other resource",
        rejected .wrongAudience elsewhere)
    , (s!"{label}: an operation needing more scope is told which",
        rejected (.insufficientScope [⟨"files:write"⟩]) underscoped)
    , (s!"{label}: the challenge names the scope the operation needs",
        (OAuth.Service.challenge (.insufficientScope [⟨"files:write"⟩])).endsWith
          "error=\"insufficient_scope\", scope=\"files:write\"")
    , (s!"{label}: a request for what was already consented to is not asked again",
        secondCode.isSome && (prompt? again).isNone)
    , (s!"{label}: the metadata document is fetched once and cached",
        fetchesAfter - fetchesBefore == 1)
    , (s!"{label}: a code redeemed once cannot be redeemed again",
        secondTokens.toOption.isSome && (replayed.toOption).isNone)
    , (s!"{label}: replaying a code revokes what the grant issued",
        rejected .revoked afterReplay)
    , (s!"{label}: a wrong code verifier is refused",
        (wrongVerifier.toOption).isNone)
    , (s!"{label}: a refresh token exchanges for a new pair",
        refreshed.toOption.isSome && (refreshed.toOption.bind (·.refreshToken)).isSome)
    , (s!"{label}: the rotated refresh token no longer works",
        (replayedRefresh.toOption).isNone)
    , (s!"{label}: presenting a rotated refresh token revokes the grant",
        rejected .revoked afterRefreshReplay)
    , (s!"{label}: a loopback redirect on an unregistered port is accepted",
        ((location ephemeral).map (·.startsWith "http://127.0.0.1:59999/callback?")) == some true)
    , (s!"{label}: a loopback redirect on another path is not",
        refusal wrongPath == some .invalidRequest)
    , (s!"{label}: the port is ignored for loopback hosts and for nothing else",
        refusal notLoopback == some .invalidRequest)
    , (s!"{label}: a dynamic registration is issued an identifier that is not a URL",
        !dynamicId.isEmpty && (ClientId.metadataDocumentUrl? ⟨dynamicId⟩).isNone)
    , (s!"{label}: a dynamically registered client reaches the same flow",
        (prompt? dynamicAsked).isSome && dynamicTokens.toOption.isSome)
    , (s!"{label}: an unknown client is refused without a redirect",
        refusal unknown == some .invalidClient)
    , (s!"{label}: a client identifier naming a private address is refused",
        refusal privateHost == some .invalidClient)
    , (s!"{label}: a request with no resource is refused as invalid_target",
        (location noResource).bind (queryValue · "error") == some "invalid_target")
    , (s!"{label}: an error response carries iss too",
        (location noResource).bind (queryValue · "iss") == some issuer)
    , (s!"{label}: plain is not a challenge method this server accepts",
        (location plainChallenge).bind (queryValue · "error") == some "invalid_request")
    , (s!"{label}: unused dynamic registrations can be pruned",
        pruned == 1 && prunedClient.isNone)
    , (s!"{label}: a request naming no scope is asked about rather than granted silently",
        (prompt? scopeless).isSome)
    , (s!"{label}: and the page is told the request named nothing",
        (prompt? scopeless).map (·.requestedScopes) == some [])
    , (s!"{label}: a request naming no scope is asked about even where a consent stands",
        bothGranted.isSome && (prompt? scopelessAgain).isSome)
    , (s!"{label}: a request within a standing consent is still not asked about again",
        (location narrower).bind (queryValue · "code") |>.isSome)
    , (s!"{label}: an approval that narrows to nothing is a refusal",
        approvedNothing.bind (queryValue · "error") == some "access_denied")
    , (s!"{label}: and it records no consent",
        !afterApprovingNothing.any fun entry => entry.subject == emptySubject)
    , (s!"{label}: a page supplying a default scope set has that set issued",
        (defaulted.toOption.map (·.scope)) == some [⟨"files:read"⟩])
    , (s!"{label}: and the code carries exactly what the entry beside it records",
        (Authentication.Consent.latest afterDefaults emptySubject).map (·.version)
          == some (Scope.render ((defaulted.toOption.map (·.scope)).getD [])))
    , (s!"{label}: a code that permits nothing is refused rather than exchanged",
        tokenError emptyCodeTokens == some .invalidGrant)
    , (s!"{label}: a refresh token that permits nothing is refused rather than rotated",
        tokenError emptyRefreshTokens == some .invalidGrant)
    , (s!"{label}: the grant is a consent record",
        history.any fun entry =>
          entry.subject == Consent.subject ⟨clientDocumentUrl⟩ ⟨resource⟩
            && entry.version == "files:read" && entry.act == .granted) ]

/-- The worked example in RFC 7636 Appendix B. Every other claim about `S256` here compares
the transform against itself, and this is the one that compares it against somebody else. -/
def pkceChecks : List (String × Bool) :=
  [ ("oauth: the S256 transform matches the worked example in RFC 7636",
      Pkce.challengeOf "dBjftJeZ4CVP-mB92K27uhbUJU1p1r_wW1gFWFOEjXk"
        == "E9Melhoa2OwvFrEMTJguCHaoeK1t8URWbuGJSstw-cM") ]

/-! ## The backends -/

def sqliteChecks : IO (List (String × Bool)) := do
  let db ← Sqlite.openInMemory
  db.exec sqliteSchemaSql
  checks "oauth" (Sqlite.store db) (sqlOAuthStore Sqlite.dialect (Sqlite.connection db))

/-- The reference backend runs the same statements. Failing to reach it is reported as a failure
rather than a skip, for the reason `Tests.Postgres` gives. -/
def postgresChecks : IO (List (String × Bool)) := do
  match ← (do
      let connection ← Authentication.Postgres.connect (← Tests.Postgres.conninfo)
      Authentication.Postgres.createSchema connection
      _root_.Postgres.execScript connection.conn postgresSchemaSql
      checks "oauth postgres" (Authentication.Postgres.store connection)
        (sqlOAuthStore Authentication.Postgres.dialect
          (Authentication.Postgres.connection connection))).toBaseIO with
  | .ok results => pure results
  | .error e => pure [(s!"oauth postgres: the reference backend was reachable ({e})", false)]

end Tests.OAuth
