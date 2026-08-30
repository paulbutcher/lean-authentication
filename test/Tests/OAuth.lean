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

/--
Folding the pairwise comparison of a list against itself leaves the accumulator alone. This is
the whole content of the theorem below, isolated so that the induction can generalise over the
accumulator, which the statement about `ByteArray` cannot.

`l` is the byte list and `b` the value the fold starts from, left arbitrary so the induction step
can apply the hypothesis at the value the previous step produced. `List.zipWith (fun x y => x ==
y) l l` pairs the list with itself, so every element compares equal and every result is `true`,
and folding `Bool.and` over `true`s returns `b` unchanged. It is stated as an equality with `b`
rather than with `true` for exactly that reason.
-/
private theorem zipWith_self_foldl (l : List UInt8) (b : Bool) :
    (List.zipWith (fun x y => x == y) l l).foldl Bool.and b = b := by
  induction l generalizing b with
  | nil => simp
  | cons x xs ih =>
    simp only [List.zipWith_cons_cons, List.foldl_cons, beq_self_eq_true, Bool.and_true, ih]

/--
Comparing every byte is what makes a verifier check free of an early exit, and an early exit is
what would report how long a correct prefix a guess had. This is the half of the claim a theorem
can reach: that the comparison written to avoid one still accepts what it should.

`a` is an arbitrary `ByteArray` and `Crypto.bytesEqual` is the constant-time comparison. The
conclusion is that it answers `true` on equal arrays, so `pkce_accepts_its_own_challenge` below
can rest on it. The converse, that it answers `false` on unequal ones, is `bytesEqual_iff` in
`Tests.Digest`; what is needed here is only that a correct verifier is not turned away.
-/
theorem bytesEqual_self (a : ByteArray) : Crypto.bytesEqual a a = true := by
  unfold Crypto.bytesEqual
  simp only [beq_self_eq_true, Bool.true_and, zipWith_self_foldl]

/--
The PKCE transform and the comparison agree: whatever the verifier, the challenge derived from it
is the one that accepts it. A mismatch would not be a subtle failure; every authorization would
fail at the token endpoint, and the temptation would be to weaken the check.

`Pkce.challengeOf` is what a client computes and sends with its authorization request, and
`Pkce.verify` is what this server runs when the verifier arrives at the token endpoint. The
conclusion is that verification answers `true` for the pair. `verifier` is an arbitrary string,
with no restriction on length or alphabet, so this is agreement between the two functions rather
than agreement on the values that were tried. That a wrong verifier is rejected is not stated
here; it is the collision resistance of the hash, which nothing in this codebase proves.
-/
theorem pkce_accepts_its_own_challenge (verifier : String) :
    Pkce.verify (Pkce.challengeOf verifier) verifier = true := by
  simp only [Pkce.verify]
  exact bytesEqual_self _

/--
The port-agnostic match admits no host that is not a loopback address. Everything else about a
redirect URI is compared as a string, so this is the whole of the exception, and an exception
that admitted a host on the internet would hand authorization codes to it.

`Uri.loopback?` reads a URI and returns `some host` when it is one this exception covers. `h`
says the read succeeded, so the claim is about URIs the function accepted. The conclusion is
that the host is in `Uri.loopbackHosts`, the fixed list of addresses that resolve to the machine
itself. Nothing is assumed about `uri`'s scheme, path or port, so a URI that dresses a public
host up in any other way still has to pass this check.
-/
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

/--
And the port-agnostic match is reached only when both URIs are loopback ones, so no pair of
ordinary URIs can match on anything but the string comparison. This is what confines the whole
exception to addresses that cannot be reached from the internet.

`Uri.matchesIgnoringPort` is the comparison used for a registered redirect URI against a
presented one. `h` says it answered `true`. The existential produces the loopback readings of
both URIs together with the fact that each host is in `Uri.loopbackHosts`. So a match that
ignored the port implies both sides parsed as loopback, which with `loopback_is_loopback` above
means neither host is a public one. Whether the rest of either URI matched is not stated here;
that part is the string comparison the function does anyway.
-/
theorem matchesIgnoringPort_is_loopback {registered presented : String}
    (h : Uri.matchesIgnoringPort registered presented = true) :
    ∃ r p, Uri.loopback? registered = some r ∧ Uri.loopback? presented = some p
      ∧ Uri.loopbackHosts.contains r.host = true ∧ Uri.loopbackHosts.contains p.host = true := by
  unfold Uri.matchesIgnoringPort at h
  split at h
  · rename_i r p heqr heqp
    exact ⟨r, p, heqr, heqp, loopback_is_loopback heqr, loopback_is_loopback heqp⟩
  · simp at h

/--
An authorization code is redeemed at most once. The store's compare-and-set is conditioned on
the stamp this writes, so what holds of the state here holds of two concurrent requests.

`AuthorizationCode.redeem` takes the moment and the code and returns the code as it now stands.
`h` says a first redemption at `now` succeeded and produced `next`. The conclusion is that
redeeming `next` fails with `.alreadyRedeemed` exactly, rather than with some error a caller
might read as an ordinary failure. `later` is an arbitrary moment and is not required to be
after `now`, so a clock that runs backwards does not reopen the code.
-/
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

/--
A rotated refresh token is dead in the same way as a redeemed code. Refresh tokens are long
lived, so one that could be rotated twice would give a stolen copy an indefinite life alongside
the legitimate holder's.

`RefreshToken.rotate` exchanges a token for its successor, and `h` says one rotation succeeded,
leaving `next`. The conclusion is that rotating `next` fails with `.alreadyRedeemed` exactly, so
the caller can tell reuse from an expired or unknown token, which is what detects a stolen copy.
`later` is any moment, earlier ones included, so no clock skew reopens it. Nothing here says the
rotation's successor cannot itself be rotated once; `next` is the token this rotation retired.
-/
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

/--
A token's audience is the `resource` its request named, at every step between the two. This is
the first of those steps: the code a grant decision mints names the resource the decision was
about, so a code cannot be spent at an audience the person was never asked about.

`decision.code` mints an authorization code from a grant decision, taking the digest of the code
value, the moment, and the lifetime. The conclusion equates the code's `resource` with the
decision's. None of `digest`, `now` or `lifetime` appears on either side, so nothing about the
minting can substitute an audience. It holds by `rfl`, so this is the definition rather than a
consequence that a later edit could quietly break without failing here.
-/
theorem code_audience_is_the_named_resource {tenant : TenantId} (decision : GrantDecision tenant)
    (digest : Digest) (now : Timestamp) (lifetime : Duration) :
    (decision.code digest now lifetime).resource = decision.resource := rfl

/--
And the entitlement a redeemed code becomes carries the code's resource, which is the second of
the three steps the audience has to survive.

`code.entitlement` is what redemption turns an authorization code into, the value a refresh
token is later rotated against. The conclusion equates its `resource` with the code's. `code` is
any authorization code, so this holds however the code was minted. It holds by `rfl`, so the
resource is carried rather than re-derived.
-/
theorem entitlement_keeps_the_audience {tenant : TenantId} (code : AuthorizationCode tenant) :
    code.entitlement.resource = code.resource := rfl

/--
And the access token minted from an entitlement carries the entitlement's resource, which is the
last of the three steps between the request and the credential a resource server sees.

`entitlement.accessToken` mints the token from the digest of its value, the moment, and the
lifetime. The conclusion equates the token's `resource` with the entitlement's. `digest`, `now`
and `lifetime` are unconstrained, so nothing supplied at the token endpoint can move the
audience. It holds by `rfl`.
-/
theorem access_token_audience {tenant : TenantId} (entitlement : Entitlement tenant)
    (digest : Digest) (now : Timestamp) (lifetime : Duration) :
    (entitlement.accessToken digest now lifetime).resource = entitlement.resource := rfl

/--
And an audience is used for nothing else: a token accepted at an audience is a token issued for
it. The three theorems above carry the resource forward; this is the check at the far end that
gives them their force, since without it a token could be presented anywhere.

`AccessToken.admits` is what a resource server calls, taking the moment, the audience it is
answering for, and the scopes it requires. `h` restricts the claim to acceptance. The conclusion
is that the token's own `resource` is that audience, so a token minted for one resource is
refused by every other. `required` and `now` are unconstrained: the theorem says nothing about
scope or expiry, which are separate branches of the same check.
-/
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

/--
An issued token's scopes are a subset of those consented to. The scopes a client asks for at the
token endpoint are its own claim, so a code that carried more than the person agreed to would
turn a consent page into a formality.

`decision.code` mints the authorization code from a grant decision, and `decision.consentedScopes`
is what the person agreed to. `Scope.subset` answers `true` when every scope of the first list
occurs in the second, so the conclusion says the code's scopes are contained in the consented
ones. `digest`, `now` and `lifetime` are unconstrained, so nothing about the minting moment or
the credential can widen the set.
-/
theorem code_scopes_were_consented {tenant : TenantId} (decision : GrantDecision tenant)
    (digest : Digest) (now : Timestamp) (lifetime : Duration) :
    Scope.subset (decision.code digest now lifetime).scopes decision.consentedScopes = true := by
  simp [GrantDecision.code, Scope.subset, Scope.granted, List.all_eq_true]

/--
And an access token minted from an entitlement carries that entitlement's scopes, so the
narrowing done at consent is the last one: nothing is added between the code and the token.

`entitlement.accessToken` is the mint, taking the digest of the token value, the moment and the
lifetime. The conclusion equates the token's `scopes` with the entitlement's. `digest`, `now` and
`lifetime` are unconstrained and none of them can move the scopes. It holds by `rfl`, so the
field is carried across rather than recomputed from anything the request supplied.
-/
theorem access_token_scopes {tenant : TenantId} (entitlement : Entitlement tenant)
    (digest : Digest) (now : Timestamp) (lifetime : Duration) :
    (entitlement.accessToken digest now lifetime).scopes = entitlement.scopes := rfl

/--
A consent that is recorded as granted grants something. An approval that narrows away to nothing
takes the refusal path instead, so no entry is ever written whose scopes reach nothing and which
every later request would then read back as a standing consent.

`ConsentDecision.settled` reduces an answer to the scopes to record, or `none` for a refusal.
`h` says it returned `some scopes`, so this is about entries that are actually written. The
conclusion is that `scopes` is not empty. The value being `some` is what carries the meaning: a
refusal and an approval that survived nothing are both `none`, so the two cases a later reader
must not confuse are collapsed deliberately rather than left to be distinguished by an empty
list.
-/
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

/--
A recorded consent grants no more than was asked for: what is recorded is a subset of what the
page displayed, whatever the host passes back. The host supplies the approved set from a form it
parsed, so without this a request could record a consent to scopes the person never saw.

`decision.settled` is the answer reduced to what should be recorded, and `h` restricts the claim
to the case where something is. `decision.prompt.requestedScopes` is what the page displayed, and
`Scope.subset` answers `true` when every element of the first list is in the second. So the
recorded set is contained in the displayed one. The empty case cannot make this vacuous, because
`settled_grants_something` above rules out an empty result, and the containment is what
`settled` computes by filtering rather than something checked afterwards.
-/
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

/-- The boolean of a JSON field, which the claim about the fetcher below is about. -/
private def flagged (document : Json) (field : String) : Option Bool :=
  match (document.getObjVal? field).toOption with
  | some (.bool value) => some value
  | _ => none

/--
The metadata document always advertises `S256`, whatever the configuration. A client that does
not find `code_challenge_methods_supported` must refuse to proceed, so this is the field that
decides whether this server is usable at all.

`advertised` reads a JSON array field back as its strings. The conclusion is the singleton
`["S256"]`, which says both that the strong method is offered and that the plain one is not, so
a client cannot be talked down to it. `documents` is the optional metadata fetcher and `config`
the deployment's own settings; both are unconstrained, so this holds of every deployment. It
holds by `rfl`, so the field is a constant of the document rather than something derived that
could come out empty.
-/
theorem metadata_advertises_s256 {m : Type → Type} (documents : Option (ClientDocuments m))
    {tenant : TenantId} (config : OAuthConfig tenant) :
    advertised (metadataDocument documents config) "code_challenge_methods_supported"
      = ["S256"] := rfl

/--
The metadata document always offers `"none"`, whatever else it offers: a public client needs it
whether or not this deployment can fetch a metadata document. An MCP client has no secret to
present, so a server advertising only authenticated methods is one it cannot use.

`advertised` reads a JSON array field back as its strings, and the field is
`token_endpoint_auth_methods_supported`. The conclusion is the singleton `["none"]`, so the
method is not merely present but the only one, and a client need not choose. `documents`,
`config` and `tenant` are all unconstrained, so no configuration removes it. It holds by `rfl`.
-/
theorem metadata_offers_public_clients {m : Type → Type} (documents : Option (ClientDocuments m))
    {tenant : TenantId} (config : OAuthConfig tenant) :
    advertised (metadataDocument documents config) "token_endpoint_auth_methods_supported"
      = ["none"] := rfl

/--
Whether a client may use a URL as its identifier is a fact about this deployment's fetcher
rather than about the protocol, and the document reports that port: the flag is `true` exactly
where a fetcher is wired, so what is advertised and what can be resolved cannot disagree.

`documents` is the optional port that fetches a client's metadata document, and `flagged` reads
a boolean field out of the JSON. The conclusion equates the advertised
`client_id_metadata_document_supported` with `documents.isSome`, so the field is `true` when a
fetcher is present and `false` when it is not, rather than being absent in either case. `config`
and `tenant` are unconstrained, so no deployment can advertise the capability by configuration
alone. It holds by `rfl`, so the document is built from the port rather than checked against it.
-/
theorem metadata_flag_follows_the_fetcher {m : Type → Type}
    (documents : Option (ClientDocuments m)) {tenant : TenantId} (config : OAuthConfig tenant) :
    flagged (metadataDocument documents config) "client_id_metadata_document_supported"
      = some documents.isSome := rfl

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

/-- What a refusal tells whoever is reading it, rather than the code a client acts on. -/
private def reason {tenant : TenantId} : OAuth.Service.Outcome tenant → Option String
  | .refuse error => some error.description
  | _ => none

private def mentions (text word : String) : Bool := (text.splitOn word).length > 1

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
  let ports : OAuth.Service.Ports IO := { store, oauth, documents := some documents, peppers }
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
  -- The same identifier against a deployment with no fetcher wired, and against one whose
  -- fetcher has nothing to offer. Both are invalid_client, and the reasons must not read alike:
  -- one is what this server does not do, the other is a request that failed.
  let noFetcher ← OAuth.Service.authorize { ports with documents := none } config
    (authorizeParams clientDocumentUrl webRedirect "files:read") session
  let fetchFailed ← OAuth.Service.authorize ports config
    (authorizeParams "https://other.example.test/client.json" webRedirect "files:read") session
  -- What the document offers, against what the flow does with the offer, for this deployment and
  -- for the same one with the fetcher taken out.
  let mechanism := "client_id_metadata_document_supported"
  let offered := flagged (metadataDocument ports.documents config) mechanism
  let withheld := flagged (metadataDocument (none : Option (ClientDocuments IO)) config) mechanism
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
    , (s!"{label}: a URL client identifier is refused where no fetcher is wired",
        refusal noFetcher == some .invalidClient && refusal fetchFailed == some .invalidClient)
    , (s!"{label}: and the refusal names the mechanism rather than a fetch that failed",
        (reason noFetcher).any (mentions · "register") && reason noFetcher != reason fetchFailed)
    , (s!"{label}: the document offers the mechanism exactly where the flow honours it",
        offered == some firstPrompt.isSome && withheld == some (prompt? noFetcher).isSome)
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

/-! ## What an account can be shown it has connected -/

private def resourceA : String := "https://a.example.test/mcp"
private def resourceB : String := "https://b.example.test/mcp"
private def resourceC : String := "https://c.example.test/mcp"
private def resourceD : String := "https://d.example.test/mcp"

private def rowFor {tenant : TenantId} (rows : List (OAuth.Service.Connection tenant))
    (client resource : String) : Option (OAuth.Service.Connection tenant) :=
  rows.find? fun row => row.client.value == client && row.resource.value == resource

/--
The listing a privacy page renders, against whichever backend it is handed.

Built against the store rather than driven through `authorize`, because the cases that decide
whether the listing is honest are ones the flow will not produce: a grant whose credentials have
lapsed, a grant with no consent entry beside it, and somebody else's grant.
-/
def connectionChecks (label : String) (store : AuthStore IO) (oauth : OAuthStore IO) :
    IO (List (String × Bool)) := do
  let tenant : TenantId := ⟨label ++ "-connections"⟩
  let ports : OAuth.Service.Ports IO := { store, oauth, documents := some documents, peppers }
  oauth.deleteTenant tenant
  store.deleteTenant tenant
  let now ← clockRef.get
  let live : Timestamp := ⟨now.epochSeconds + 3600⟩
  let lapsed : Timestamp := ⟨now.epochSeconds - 1⟩
  let account : AccountId tenant := ⟨"account-1"⟩
  let other : AccountId tenant := ⟨"account-2"⟩
  for holder in [account, other] do
    let person := address s!"{holder.value}@example.com"
    discard <| store.createAccount tenant
      { id := holder
        identity := person.normalise
        primaryEmail := person
        createdAt := now }
  let dynamicId : ClientId := ⟨"a-registered-client"⟩
  oauth.createClient tenant
    { id := dynamicId
      metadata := { clientName := "Legacy Client", redirectUris := [webRedirect] }
      registeredAt := now
      lastUsedAt := now }
  oauth.cacheDocument tenant
    { client := ⟨clientDocumentUrl⟩
      metadata := { clientName := "Example MCP Client", redirectUris := [webRedirect] }
      fetchedAt := now
      freshUntil := live }
  -- One credential of each kind per grant, so that a grant's two rows share its identifier the
  -- way the flow would have written them.
  let access : AccountId tenant → String → ClientId → String → List Scope → Timestamp →
      IO Unit :=
    fun holder grant client target scopes expiresAt =>
      oauth.createAccessToken tenant
        { grant := ⟨grant⟩
          digest := peppers.current.digest ⟨grant ++ "-access"⟩
          account := holder, client, resource := ⟨target⟩, scopes, issuedAt := now, expiresAt }
  let refresh : AccountId tenant → String → ClientId → String → List Scope → Timestamp →
      Option Timestamp → IO Unit :=
    fun holder grant client target scopes expiresAt replacedAt =>
      oauth.createRefreshToken tenant
        { grant := ⟨grant⟩
          digest := peppers.current.digest ⟨grant ++ "-refresh"⟩
          account := holder, client, resource := ⟨target⟩, scopes, issuedAt := now, expiresAt,
          replacedAt }
  let consented : ClientId → String → String → IO Unit :=
    fun client target version =>
      store.recordConsent tenant
        { account
          subject := Consent.subject client ⟨target⟩
          version
          act := .granted
          recordedAt := now }
  -- A refresh token and nothing else, with no consent entry beside it.
  refresh account "g-refresh-only" dynamicId resourceA [⟨"files:read"⟩] live none
  -- The same client against a second resource.
  access account "g-second-resource" dynamicId resourceB [⟨"files:read"⟩, ⟨"files:write"⟩] live
  consented dynamicId resourceB "files:read files:write"
  -- A metadata document client against the first.
  access account "g-document" ⟨clientDocumentUrl⟩ resourceA [⟨"files:read"⟩] live
  consented ⟨clientDocumentUrl⟩ resourceA "files:read"
  -- A grant with nothing usable left: one credential expired, the other rotated away.
  access account "g-lapsed" ⟨clientDocumentUrl⟩ resourceB [⟨"files:read"⟩] lapsed
  refresh account "g-lapsed" ⟨clientDocumentUrl⟩ resourceB [⟨"files:read"⟩] live (some now)
  -- Somebody else's grant, against a client and a resource this account has nothing under.
  refresh other "g-elsewhere" dynamicId resourceC [⟨"files:read"⟩] live none
  -- A consent with no credential under it at all: nothing lists it, and it is still the account
  -- holder's to withdraw.
  consented dynamicId resourceD "files:read"
  let fetchesBefore ← fetchCount.get
  let listed ← OAuth.Service.connections ports account
  let others ← OAuth.Service.connections ports other
  let fetchesAfter ← fetchCount.get
  let revoked ← OAuth.Service.revoke ports account dynamicId ⟨resourceB⟩
  let afterRevoke ← OAuth.Service.connections ports account
  let revokedAgain ← OAuth.Service.revoke ports account dynamicId ⟨resourceB⟩
  let revokedNothing ← OAuth.Service.revoke ports account ⟨clientDocumentUrl⟩ ⟨resourceB⟩
  let revokedStanding ← OAuth.Service.revoke ports account dynamicId ⟨resourceD⟩
  let history ← store.consentHistory tenant account
  let withdrawals : ClientId → String → Nat := fun client target =>
    (history.filter fun entry =>
      entry.subject == Consent.subject client ⟨target⟩ && entry.act == .withdrawn).length
  let refreshOnly := rowFor listed dynamicId.value resourceA
  let document := rowFor listed clientDocumentUrl resourceA
  pure
    [ (s!"{label}: a grant with a live refresh token is listed", refreshOnly.isSome)
    , (s!"{label}: one whose credentials have all lapsed is not, expired and rotated alike",
        (rowFor listed clientDocumentUrl resourceB).isNone)
    , (s!"{label}: a grant with no consent entry beside it is listed all the same",
        (refreshOnly.map (·.since)) == some none)
    , (s!"{label}: a row carries the credential's scopes",
        (refreshOnly.map (·.scopes)) == some [⟨"files:read"⟩])
    , (s!"{label}: one client against two resources is two rows",
        (rowFor listed dynamicId.value resourceB).isSome
          && (listed.filter (·.client == dynamicId)).length == 2)
    , (s!"{label}: two clients against one resource is two rows",
        document.isSome && (listed.filter (·.resource.value == resourceA)).length == 2)
    , (s!"{label}: a dynamic registration is named by what it registered",
        (refreshOnly.map fun row => (row.clientName, row.origin))
          == some (some "Legacy Client", ClientOrigin.dynamic))
    , (s!"{label}: a metadata document client is named from the cache, and nothing is fetched",
        (document.map fun row => (row.clientName, row.origin))
            == some (some "Example MCP Client", ClientOrigin.metadataDocument)
          && fetchesAfter == fetchesBefore)
    , (s!"{label}: a row says when the consent behind it was recorded",
        (rowFor listed dynamicId.value resourceB |>.map (·.since)) == some (some now))
    , (s!"{label}: another account's grants are not listed",
        listed.all (·.resource.value != resourceC)
          && others.map (fun row => (row.client.value, row.resource.value))
            == [(dynamicId.value, resourceC)])
    , (s!"{label}: revoking a grant takes its row with it",
        revoked && (rowFor afterRevoke dynamicId.value resourceB).isNone
          && afterRevoke.length == 2)
    , (s!"{label}: revoking it again reports nothing to withdraw and records nothing",
        !revokedAgain && withdrawals dynamicId resourceB == 1)
    , (s!"{label}: a lapsed grant with no consent behind it is nothing to withdraw",
        !revokedNothing && withdrawals ⟨clientDocumentUrl⟩ resourceB == 0)
    , (s!"{label}: a consent outliving its credentials is withdrawable all the same",
        revokedStanding && withdrawals dynamicId resourceD == 1
          && !Authentication.Consent.granted history (Consent.subject dynamicId ⟨resourceD⟩)) ]

/-- The worked example in RFC 7636 Appendix B. Every other claim about `S256` here compares
the transform against itself, and this is the one that compares it against somebody else. -/
def pkceChecks : List (String × Bool) :=
  [ ("oauth: the S256 transform matches the worked example in RFC 7636",
      Pkce.challengeOf "dBjftJeZ4CVP-mB92K27uhbUJU1p1r_wW1gFWFOEjXk"
        == "E9Melhoa2OwvFrEMTJguCHaoeK1t8URWbuGJSstw-cM") ]

/-! ## The refusal as a document -/

private def protectedResourceMetadata : String :=
  "https://mcp.example.test/.well-known/oauth-protected-resource"

/-- The value of one `WWW-Authenticate` parameter, found the way a client finds it: `name="` and
everything up to the closing quote. -/
private def headerParam (header name : String) : Option String :=
  let rec scan (marker : List Char) : List Char → Option (List Char)
    | [] => none
    | c :: rest =>
      if (c :: rest).take marker.length == marker then
        some (((c :: rest).drop marker.length).takeWhile (· != '"'))
      else scan marker rest
  (scan (name.toList ++ ['=', '"']) header.toList).map String.ofList

private def documentMember (document : Json) (name : String) : Option String :=
  match (document.getObjVal? name).toOption with
  | some (.str value) => some value
  | _ => none

private def everyRejection : List AccessToken.Rejection :=
  [.unknown, .expired, .revoked, .wrongAudience,
    .insufficientScope [⟨"files:read"⟩, ⟨"files:write"⟩]]

/-- The header and the document are one mapping with two outputs, and what a deployment behind a
hop that renames headers reads is whichever of them survived. A code or a scope in one and not
the other is a client acting on less than it was told.

`everyRejection` is every constructor; one added to `Rejection` belongs there too. -/
def refusalChecks : List (String × Bool) :=
  everyRejection.map (fun rejection =>
    let header := OAuth.Service.challenge rejection protectedResourceMetadata
    let document := OAuth.Service.refusalDocument rejection protectedResourceMetadata
    (s!"oauth: the document says what the header says about {repr rejection}",
      (headerParam header "error").isSome
        && headerParam header "error" == documentMember document "error"
        && headerParam header "scope" == documentMember document "scope"
        && headerParam header "resource_metadata" == documentMember document "resource_metadata"))
  ++ [ ("oauth: the four invalid_token refusals are told apart by their descriptions",
          (([.unknown, .expired, .revoked, .wrongAudience] : List AccessToken.Rejection).filterMap
            fun rejection =>
              documentMember (OAuth.Service.refusalDocument rejection) "error_description").eraseDups.length
            == 4)
     , ("oauth: a document with nowhere to send a client omits resource_metadata rather than guessing",
          (documentMember (OAuth.Service.refusalDocument .unknown) "resource_metadata").isNone) ]

/-! ## The operator's name for a refusal -/

private def everyGrantRejection : List GrantRejection :=
  [.unknown, .expired, .alreadyRedeemed, .revoked, .clientMismatch, .redirectMismatch,
    .resourceMismatch, .verifierMismatch, .scopeExceeded]

private def everyMetadataRejection : List MetadataRejection :=
  [.notAnObject, .clientIdMismatch, .missingName, .missingRedirectUris, .unusableRedirectUri,
    .unsupportedAuthMethod, .unsupportedGrantType, .unsupportedResponseType]

private def named (names : List String) : Bool :=
  names.all (!·.isEmpty) && names.eraseDups.length == names.length

/--
Every refusal these three types express has a name of its own for whoever is reading a log. Both
halves matter and for different reasons: an empty name is a log line that says a refusal
happened and not which, and a shared one is two causes a query cannot separate, which is the
whole reason the names exist where the code the client is told already collapses them.

`named` answers `true` when no name in a list is empty and no two are equal, and each list is
every constructor of one type mapped through its `name`. The three lists are written out rather
than derived, so a constructor added to a type and not to the list beside it is the one thing
this does not catch. `insufficientScope` carries scopes and the representative in
`everyRejection` carries two of them, which loses nothing: `name` does not read them.
-/
theorem rejection_names_are_distinct :
    named (everyRejection.map AccessToken.Rejection.name)
      ∧ named (everyGrantRejection.map GrantRejection.name)
      ∧ named (everyMetadataRejection.map MetadataRejection.name) := by
  decide

/-! ## The consent form -/

/-- A scope holding everything an unencoded field name would break on. -/
private def trickyScope : Scope := ⟨"files:read/write =now"⟩

/--
Whatever the client put in the scope, what reaches the form is a name a browser will send back
and a lookup will find. A scope is an opaque string the client chose, so a page naming its
fields after scopes directly would let the client choose the field names.

`trickyScope` holds a slash, a space and an equals sign, which is what an unencoded field name
would break on. `approvalField` is the name the checkbox is given, and the conclusion is that
every character of it is a letter, a digit, a hyphen or an underscore. That alphabet is the one
that survives a form encoding unchanged. One scope is not the general claim, but it is the case
that would fail first: the encoding is base64url, whose output alphabet is precisely this.
-/
theorem approval_field_is_url_safe :
    trickyScope.approvalField.toList.all
      (fun c => c.isAlpha || c.isDigit || c == '-' || c == '_') = true := by decide

/--
The encoding is written and read in one place, so the scope that comes back ticked is the one
the checkbox was about. Without this a scope whose name a browser mangles could be approved and
recorded as a different scope, or as none.

`Scope.approved` takes the scopes the page displayed and the host's lookup into the submitted
form, and returns those left ticked. Here the lookup answers `true` for exactly
`trickyScope.approvalField`, which is what a browser sends back when that one checkbox is
ticked. The conclusion is `[trickyScope]`: the awkward scope is recovered, and `files:read`,
whose box was not ticked, is not. Both halves matter, since a lookup that matched everything
would satisfy the first alone.
-/
theorem approved_reads_back_what_was_ticked :
    Scope.approved [trickyScope, ⟨"files:read"⟩] (· == trickyScope.approvalField)
      = [trickyScope] := by decide

/--
Two scopes are two fields, so the box that was ticked is the box that scope's checkbox was.
`approved_reads_back_what_was_ticked` reads one of them back; this is why it is not reading the
other.

`trickyScope` and `⟨"files:read"⟩` are two distinct scopes, and the conclusion is that their
`approvalField` names compare unequal. Injectivity in general is not claimed, only this pair;
the encoding is base64url of the scope text, so the general fact holds, but what the theorem
above needs is that these two do not collide. The case is finite, so `decide` settles it.
-/
theorem distinct_scopes_get_distinct_fields :
    (trickyScope.approvalField == Scope.approvalField ⟨"files:read"⟩) = false := by decide

/-! ## A default for a client that named no scopes -/

/--
A deployment's own scopes stand in where a client asked for none, so a request that named
nothing produces a page with something on it rather than a consent to nothing.

`h` says the prompt's `requestedScopes` is empty, which is the silence in question. The
conclusion is that the prompt's scopes are then `defaults` exactly, so what the person is asked
about is what the deployment chose, neither narrowed nor added to. `defaults` is unconstrained
and may itself be empty, in which case the page still asks about nothing; choosing what to
default to is the deployment's business, and this says only that the choice is honoured.
-/
theorem defaults_fill_a_silence {tenant : TenantId} (prompt : OAuth.Service.ConsentPrompt tenant)
    (defaults : List Scope) (h : prompt.requestedScopes = []) :
    (prompt.withDefaultScopes defaults).requestedScopes = defaults := by
  simp [OAuth.Service.ConsentPrompt.withDefaultScopes, h]

/--
A client that named its own scopes is asked about those and no others. The default fills a
silence; it does not widen a request.

`withDefaultScopes` is what a deployment calls to put its own scopes on a consent page. `h` is
the case this theorem is about: the request named at least one scope. The conclusion is equality
of the whole prompt, not just of its scopes, so the default changes nothing else about the page
either. Together with `defaults_fill_a_silence` above the two cases are exhaustive, so the
function's whole behaviour is pinned.
-/
theorem defaults_never_widen_a_request {tenant : TenantId}
    (prompt : OAuth.Service.ConsentPrompt tenant) (defaults : List Scope)
    (h : prompt.requestedScopes ≠ []) :
    prompt.withDefaultScopes defaults = prompt := by
  simp [OAuth.Service.ConsentPrompt.withDefaultScopes, List.isEmpty_iff, h]

/-! ## The backends -/

def sqliteChecks : IO (List (String × Bool)) := do
  let db ← Sqlite.openInMemory
  db.exec sqliteSchemaSql
  let store := Sqlite.store db
  let oauth := sqlOAuthStore Sqlite.dialect (Sqlite.connection db)
  pure ((← checks "oauth" store oauth) ++ (← connectionChecks "oauth" store oauth))

/-- The reference backend runs the same statements. Failing to reach it is reported as a failure
rather than a skip, for the reason `Tests.Postgres` gives. -/
def postgresChecks : IO (List (String × Bool)) := do
  match ← (do
      let connection ← Authentication.Postgres.connect (← Tests.Postgres.conninfo)
      Authentication.Postgres.createSchema connection
      _root_.Postgres.execScript connection.conn postgresSchemaSql
      let store := Authentication.Postgres.store connection
      let oauth := sqlOAuthStore Authentication.Postgres.dialect
        (Authentication.Postgres.connection connection)
      pure ((← checks "oauth postgres" store oauth)
        ++ (← connectionChecks "oauth postgres" store oauth))).toBaseIO with
  | .ok results => pure results
  | .error e => pure [(s!"oauth postgres: the reference backend was reachable ({e})", false)]

end Tests.OAuth
