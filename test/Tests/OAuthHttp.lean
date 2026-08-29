/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import AuthenticationHttp
import AuthenticationOAuth
import AuthenticationSqlite
import Middleware.Test.Browser
import Std.Http.Test.Helpers

/-!
The authorisation server's routes, driven over the wire (§20, AUTH-16.5).

Requests go in as HTTP text and responses come back as HTTP text, through the real parser and the
real serialiser, against SQLite in memory. `Service` is tested in `Tests.OAuth`; what is tested
here is the layer above it, which is where an application's OAuth defects live.

The consent page is driven through `Middleware.Test.Browser`, which holds the cookies and scrapes
the anti-forgery token out of the rendered page before posting the form back. A consent check that
assembled the post by hand would pass whether or not the page rendered a token, which is the
failure that arrangement exists to prevent.

Where the routes answer and what the metadata document advertises are compared as theorems: both
are pure and both are finite, and a disagreement between them is silent. Everything works except
discovery by a client that constructs the URL the specification tells it to.
-/

namespace Tests.OAuthHttp
open Authentication Authentication.OAuth
open Std.Http.Internal.Test

/-! ## The paths a document advertises are the paths the routes answer on

`OAuthConfig.standard` and `OAuthConfig.atOrigin` build every endpoint URL from the origin, the
tenant's path where there is one, and the four paths below; the routes answer on patterns declared
independently of them. These are where the two meet, and a disagreement is exactly the failure
nothing observes: everything works except discovery.

Stated over an arbitrary tenant, because a check on one would pass on a table that had spliced the
tenant in at the wrong place. -/

private def base : BaseUrl := ⟨"https://auth.example.test"⟩

def tenant : TenantId := ⟨"acme"⟩

/-- The capture standing where a tenant identifier goes, so that a pattern is compared against
the path a tenant's URLs are built from rather than against a copy of itself. -/
private def anyTenant : TenantId := ⟨":tenant:String"⟩

theorem perTenantPathsAgree :
    (Routing.renderPattern OAuth.Http.PerTenant.patterns.authorize,
      Routing.renderPattern OAuth.Http.PerTenant.patterns.token,
      Routing.renderPattern OAuth.Http.PerTenant.patterns.register) =
    (BaseUrl.tenantPath anyTenant ++ OAuthConfig.authorizePath,
      BaseUrl.tenantPath anyTenant ++ OAuthConfig.tokenPath,
      BaseUrl.tenantPath anyTenant ++ OAuthConfig.registrationPath) := by decide

/-- RFC 8414 §3 puts the well-known suffix ahead of the issuer's path, and the route answers
there, so a client that constructs the URL from the issuer it was given reaches it. -/
theorem perTenantMetadataAgrees :
    Routing.renderPattern OAuth.Http.PerTenant.patterns.metadata
      = OAuthConfig.metadataPrefix ++ BaseUrl.tenantPath anyTenant := by decide

/-- At the origin the issuer has no path, so every endpoint is the bare path and the document is
at the bare suffix, which is the URL a client holding only an origin constructs. That is the whole
reason the mount is a parameter. -/
theorem atOriginPathsAgree :
    (Routing.renderPattern OAuth.Http.AtOrigin.patterns.authorize,
      Routing.renderPattern OAuth.Http.AtOrigin.patterns.token,
      Routing.renderPattern OAuth.Http.AtOrigin.patterns.register,
      Routing.renderPattern OAuth.Http.AtOrigin.patterns.metadata) =
    (OAuthConfig.authorizePath, OAuthConfig.tokenPath, OAuthConfig.registrationPath,
      OAuthConfig.metadataPrefix) := by decide

/-! ## The fakes -/

initialize clockRef : IO.Ref Timestamp ← IO.mkRef ⟨1700000000⟩
initialize drawCounter : IO.Ref Nat ← IO.mkRef 0

instance : Clock IO where
  now := clockRef.get

instance : RandomBytes IO where
  draw count := do
    let index ← drawCounter.modifyGet fun n => (n, n + 1)
    pure (.ok ((Crypto.Sha256.hashUtf8 s!"oauth-http-seed-{index}").extract 0 count))

def peppers : PepperRing :=
  { current := { keyId := ⟨"pepper-1"⟩, secret := Crypto.Sha256.hashUtf8 "test pepper" } }

private def address (raw : String) : EmailAddress := (EmailAddress.parse raw).toOption.getD default

def tenantConfig : TenantConfig tenant :=
  { displayName := "Acme"
    baseUrl := base
    sendingIdentity :=
      { address := address "sign-in@auth.example.test", displayName := "Acme sign-in" }
    signupPolicy := .unrestricted
    -- The authorization endpoint has to be a permitted `returnTo`, or a request arriving with no
    -- session signs somebody in and then lands them on the tenant's default instead of the
    -- request that sent them there.
    returnToAllowlist := [BaseUrl.tenantPath tenant ++ OAuthConfig.authorizePath] }

def oauthConfig : OAuthConfig tenant :=
  OAuthConfig.standard base [⟨"files:read"⟩, ⟨"files:write"⟩]

private def tenantResolver (t : TenantId) : IO (Option (TenantConfig t)) :=
  if h : t = tenant then pure (some (h ▸ tenantConfig)) else pure none

private def oauthResolver (t : TenantId) : IO (Option (OAuthConfig t)) :=
  if h : t = tenant then pure (some (h ▸ oauthConfig)) else pure none

def sessionCredential : CredentialValue := ⟨"session-credential"⟩

def redirectUri : String := "https://app.example.test/callback"

def resource : String := "https://mcp.example.test/mcp"

/-- Forty-three unreserved characters, which is the shortest a verifier may be. -/
def verifier : String := "verifier-verifier-verifier-verifier-verifie"

/-! ## Talking to the routes -/

private def configOn (db : SQLite) : OAuth.Http.Config :=
  { ports :=
      { store := Sqlite.store db
        oauth := sqlOAuthStore Sqlite.dialect (Sqlite.connection db)
        peppers }
    tenant := tenantResolver
    oauth := oauthResolver }

private def handlerOn (db : SQLite) : TestHandler := fun request =>
  (OAuth.Http.handler (configOn db)).onRequest request

/-- Sends one raw request and returns the raw response. A failure inside the harness comes back
as an empty response, which fails whatever was being checked rather than the whole run. -/
private def send (db : SQLite) (raw : String) : IO String := do
  let captured ← IO.mkRef ""
  try
    check "oauth-http" raw (handlerOn db) fun bytes =>
      captured.set ((String.fromUTF8? bytes).getD "")
  catch _ => pure ()
  captured.get

private def statusOf (response : String) : String :=
  ((response.splitOn "\x0d\n").head?.getD "")

private def headerValues (response : String) (name : String) : List String :=
  let head := (response.splitOn "\x0d\n\x0d\n").head?.getD ""
  ((head.splitOn "\x0d\n").drop 1).filterMap fun line =>
    match line.splitOn ":" with
    | key :: rest =>
      if key.toLower == name then some (String.intercalate ":" rest).trimAscii.toString else none
    | [] => none

private def bodyOf (response : String) : String :=
  String.intercalate "\x0d\n\x0d\n" ((response.splitOn "\x0d\n\x0d\n").drop 1)

private def contains (haystack needle : String) : Bool :=
  (haystack.splitOn needle).length > 1

private def noStore (response : String) : Bool :=
  headerValues response "cache-control" == ["no-store"]

private def locationOf (response : String) : Option String :=
  (headerValues response "location").head?

/-- What a redirect target carries under one name, read the way the client will read it. -/
private def queryValue (target : String) (name : String) : Option String :=
  ((target.splitOn "?").drop 1).head?.bind fun query =>
    (query.splitOn "&").findSome? fun pair =>
      match pair.splitOn "=" with
      | [key, value] => if key == name then some value else none
      | _ => none

private def field (body : String) (name : String) : Option String :=
  ((Json.parse body).toOption.bind (·.getObjVal? name |>.toOption)).bind fun value =>
    match value with
    | .str text => some text
    | _ => none

private def encoded (pairs : List (String × String)) : String :=
  String.intercalate "&"
    (pairs.map fun (name, value) => Uri.encodeComponent name ++ "=" ++ Uri.encodeComponent value)

private def authorizePath (params : List (String × String)) : String :=
  BaseUrl.tenantPath tenant ++ OAuthConfig.authorizePath ++ "?" ++ encoded params

private def tokenPath : String := BaseUrl.tenantPath tenant ++ OAuthConfig.tokenPath

private def registerPath : String := BaseUrl.tenantPath tenant ++ OAuthConfig.registrationPath

private def metadataPath : String :=
  OAuthConfig.metadataPrefix ++ BaseUrl.tenantPath tenant

private def formPost (path body : String) : String :=
  mkPost path body "Content-Type: application/x-www-form-urlencoded\x0d\nConnection: close\x0d\n"

private def jsonPost (path body : String) : String :=
  mkPost path body "Content-Type: application/json\x0d\nConnection: close\x0d\n"

private def registration : String :=
  "{\"client_name\":\"Widget\",\"redirect_uris\":[\"" ++ redirectUri ++ "\"]}"

/-! ## The checks -/

def checks : IO (List (String × Bool)) := do
  clockRef.set ⟨1700000000⟩
  let db ← Sqlite.openInMemory
  db.exec sqliteSchemaSql
  let config := configOn db
  let now ← clockRef.get

  -- Somebody to be signed in as, and the cookie the sign-in flow would have issued.
  let person := address "person@example.test"
  let account : AccountId tenant := ⟨"account-1"⟩
  discard <| config.ports.store.createAccount tenant
    { id := account, identity := person.normalise, primaryEmail := person, createdAt := now }
  config.ports.store.createSession tenant
    { id := ⟨"session-1"⟩
      account
      identifierDigest := peppers.current.digest sessionCredential
      createdAt := now
      lastSeenAt := now
      idleExpiresAt := ⟨now.epochSeconds + 3600⟩
      absoluteExpiresAt := ⟨now.epochSeconds + 86400⟩ }

  -- Registration, which is the only way in for a deployment with no document fetcher.
  let registered ← send db (jsonPost registerPath registration)
  let clientId := (field (bodyOf registered) "client_id").getD ""
  let asForm ← send db (formPost registerPath (encoded [("client_name", "Widget")]))
  let metadata ← send db (mkGetClose metadataPath)

  let requestParams : List (String × String) :=
    [ ("response_type", "code"), ("client_id", clientId), ("redirect_uri", redirectUri),
      ("code_challenge", Pkce.challengeOf verifier), ("code_challenge_method", "S256"),
      ("resource", resource), ("scope", "files:read files:write"), ("state", "xyzzy") ]
  let target := authorizePath requestParams

  -- The four outcomes of `authorize`.
  let unaddressable ← send db
    (mkGetClose (authorizePath (requestParams.filter (·.1 != "client_id"))))
  let unauthenticated ← send db (mkGetClose target)
  let silent ← send db
    (mkGetClose (authorizePath (requestParams ++ [("prompt", "none")])))

  -- The consent page, driven the way a browser drives it: cookies held, token scraped, form
  -- posted back to the URL it was served from.
  let browser ← Middleware.Test.Browser.new (handlerOn db)
  browser.cookies.set [("auth_session", sessionCredential.encoded)]
  let consent := String.fromUTF8! (← browser.get target)
  let heldToken ← browser.token?
  let approve (answer : String) (scopes : List Scope) : IO String := do
    pure (String.fromUTF8! (← browser.post target
      ((OAuth.ConsentForm.answerField, answer)
        :: scopes.map fun scope => (scope.approvalField, "yes"))))
  let granted ← approve OAuth.ConsentForm.approveValue [⟨"files:read"⟩]
  let code := (locationOf granted).bind (queryValue · "code")

  -- The token endpoint, which is a client's request and carries no cookie.
  let exchange : List (String × String) :=
    [ ("grant_type", "authorization_code"), ("client_id", clientId),
      -- Base64url is unreserved throughout, so the code reaches the client's query verbatim.
      ("code", code.getD ""),
      ("redirect_uri", redirectUri), ("code_verifier", verifier), ("resource", resource) ]
  let issued ← send db (formPost tokenPath (encoded exchange))
  let duplicated ← send db
    (formPost tokenPath (encoded (exchange ++ [("client_id", clientId)])))
  let notAForm ← send db (jsonPost tokenPath "{}")

  -- A second person's answer, refusing this time. The browser is fresh so that the first
  -- exchange's rotated credentials are not in play.
  let denier ← Middleware.Test.Browser.new (handlerOn db)
  denier.cookies.set [("auth_session", sessionCredential.encoded)]
  let second := authorizePath (requestParams.map fun (name, value) =>
    if name == "state" then (name, "second") else (name, value))
  discard <| denier.get second
  let denied := String.fromUTF8! (← denier.post second [(OAuth.ConsentForm.answerField, "deny")])

  let everything :=
    [ registered, asForm, metadata, unaddressable, unauthenticated, silent, consent, granted,
      issued, duplicated, notAForm, denied ]

  pure
    [ ("oauth http: a JSON registration is created", statusOf registered == "HTTP/1.1 201 Created"),
      ("oauth http: and answers with an identifier", !clientId.isEmpty),
      ("oauth http: a form-encoded registration is refused",
        statusOf asForm == "HTTP/1.1 400 Bad Request"
          && contains (bodyOf asForm) "invalid_client_metadata"),
      ("oauth http: the metadata document advertises where the routes answer",
        field (bodyOf metadata) "authorization_endpoint" == some oauthConfig.authorizationEndpoint
          && field (bodyOf metadata) "token_endpoint" == some oauthConfig.tokenEndpoint
          && field (bodyOf metadata) "registration_endpoint" == some oauthConfig.registrationEndpoint
          && field (bodyOf metadata) "issuer" == some oauthConfig.issuer),
      ("oauth http: a client that cannot be established is told to the person, not to it",
        statusOf unaddressable == "HTTP/1.1 400 Bad Request" && locationOf unaddressable == none),
      ("oauth http: a request with no session is sent to sign in",
        statusOf unauthenticated == "HTTP/1.1 302 Found"
          && (locationOf unauthenticated).any
              (contains · (BaseUrl.tenantPath tenant ++ "/signin"))),
      ("oauth http: prompt=none is refused to the client rather than asked about",
        statusOf silent == "HTTP/1.1 302 Found"
          && (locationOf silent).bind (queryValue · "error") == some "login_required"),
      ("oauth http: the consent page renders an anti-forgery token", heldToken.isSome),
      ("oauth http: and names every scope that was asked for",
        contains consent (Scope.approvalField ⟨"files:read"⟩)
          && contains consent (Scope.approvalField ⟨"files:write"⟩)),
      ("oauth http: approving returns a code to the client", code.isSome),
      ("oauth http: and carries the state it was given",
        (locationOf granted).bind (queryValue · "state") == some "xyzzy"),
      ("oauth http: the code buys a token", statusOf issued == "HTTP/1.1 200 OK"),
      ("oauth http: whose scope is what was ticked and nothing else",
        field (bodyOf issued) "scope" == some "files:read"),
      ("oauth http: a parameter sent twice is refused",
        statusOf duplicated == "HTTP/1.1 400 Bad Request"
          && contains (bodyOf duplicated) "invalid_request"),
      ("oauth http: the token endpoint reads a form and nothing else",
        statusOf notAForm == "HTTP/1.1 400 Bad Request"
          && contains (bodyOf notAForm) "invalid_request"),
      ("oauth http: denying grants nothing",
        (locationOf denied).bind (queryValue · "error") == some "access_denied"
          && (locationOf denied).bind (queryValue · "code") == none),
      ("oauth http: every response is no-store", everything.all noStore) ]

/-- The other mount. A deployment serving one tenant at the origin is discovered at the bare
well-known suffix, which is the URL a client holding only an origin constructs, and its endpoints
carry no tenant path. Driven rather than left to `atOriginPathsAgree`, because that theorem says
where the routes answer and this says that they answer. -/
def originChecks : IO (List (String × Bool)) := do
  clockRef.set ⟨1700000000⟩
  let db ← Sqlite.openInMemory
  db.exec sqliteSchemaSql
  let originConfig : OAuth.Http.Config :=
    { configOn db with
      mountedAt := .origin tenant
      oauth := fun t =>
        if h : t = tenant then
          pure (some (h ▸ (OAuthConfig.atOrigin base [⟨"files:read"⟩] : OAuthConfig tenant)))
        else pure none }
  let handler : TestHandler := fun request => (OAuth.Http.handler originConfig).onRequest request
  let fetch (path : String) : IO String := do
    let captured ← IO.mkRef ""
    try
      check "oauth-http-origin" (mkGetClose path) handler fun bytes =>
        captured.set ((String.fromUTF8? bytes).getD "")
    catch _ => pure ()
    captured.get
  let document ← fetch OAuthConfig.metadataPrefix
  let belowTheTenant ← fetch metadataPath
  pure
    [ ("oauth http: an origin mount is discovered at the bare well-known suffix",
        statusOf document == "HTTP/1.1 200 OK"
          && field (bodyOf document) "issuer" == some base.origin
          && field (bodyOf document) "authorization_endpoint"
              == some (base.origin ++ OAuthConfig.authorizePath)),
      ("oauth http: and answers nowhere else",
        statusOf belowTheTenant == "HTTP/1.1 404 Not Found") ]

/-- The consent form is unpostable without the token the page carried, which is the whole of what
stops another site posting the answer. Driven separately because `Browser` refuses to make a
request a browser could not, which is what makes it the right harness for the case above. -/
def antiForgeryChecks : IO (List (String × Bool)) := do
  clockRef.set ⟨1700000000⟩
  let db ← Sqlite.openInMemory
  db.exec sqliteSchemaSql
  let config := configOn db
  let now ← clockRef.get
  let person := address "person@example.test"
  let account : AccountId tenant := ⟨"account-1"⟩
  discard <| config.ports.store.createAccount tenant
    { id := account, identity := person.normalise, primaryEmail := person, createdAt := now }
  config.ports.store.createSession tenant
    { id := ⟨"session-1"⟩
      account
      identifierDigest := peppers.current.digest sessionCredential
      createdAt := now
      lastSeenAt := now
      idleExpiresAt := ⟨now.epochSeconds + 3600⟩
      absoluteExpiresAt := ⟨now.epochSeconds + 86400⟩ }
  let registered ← send db (jsonPost registerPath registration)
  let clientId := (field (bodyOf registered) "client_id").getD ""
  let target := authorizePath
    [ ("response_type", "code"), ("client_id", clientId), ("redirect_uri", redirectUri),
      ("code_challenge", Pkce.challengeOf verifier), ("code_challenge_method", "S256"),
      ("resource", resource), ("scope", "files:read") ]
  let cookie := s!"Cookie: auth_session={sessionCredential.encoded}\x0d\n"
  let forged ← send db
    (mkPost target (encoded [(OAuth.ConsentForm.answerField, OAuth.ConsentForm.approveValue)])
      ("Content-Type: application/x-www-form-urlencoded\x0d\n" ++ cookie
        ++ "Connection: close\x0d\n"))
  pure
    [ ("oauth http: a consent form posted without the page's token is refused",
        statusOf forged == "HTTP/1.1 403 Forbidden" && locationOf forged == none),
      ("oauth http: and the refusal is still no-store", noStore forged) ]

end Tests.OAuthHttp
