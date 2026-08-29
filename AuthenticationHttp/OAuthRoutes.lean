/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import AuthenticationHttp.OAuthPages
public import AuthenticationHttp.Routes
public import AuthenticationOAuth.Metadata
public import AuthenticationOAuth.Service
public import Routing
import Crypto.Compare
import Middleware

/-!
The authorisation server's own endpoints (§20).

`Service` decides everything; what is here is the transport, which is the layer an application's
OAuth defects actually live in. Each of these is invisible when it is wrong:

- **`Cache-Control: no-store` on every response** (OAuth 2.1 §3.2.3). Tokens are the reason, and
  a consent page naming somebody's account is a second one.
- **Duplicates are preserved** on the way in (§4.1.1), which is what lets a parameter sent twice
  be refused. `Params.ofQuery` does it, and it decodes once, so nothing downstream compares a
  percent-encoded name against a decoded one.
- **A query and a form body are read apart and never merged.** A token request that took a
  parameter from the query string would be reading one the client did not agree to send there.
- **The `POST` to `/oauth/authorize` re-reads the request** rather than reassembling it from
  hidden fields. The form posts back to the URL it was served from, and running `authorize`
  again on the way through is what makes what is concluded the request as it arrived. It costs a
  client lookup, which is cached.

Nothing in front of `authorize` decides whether somebody is signed in. `authorize` decides it,
because the answer is sometimes a redirect to the client rather than a sign-in page: `prompt=none`
is a request that must be refused rather than asked about, and a guard would ask.
-/

public section

namespace Authentication.OAuth.Http

open Std.Http
open Std.Async
open Std.Http.Server

/-! ## Where the endpoints answer -/

/--
Which of the two shapes the endpoints are mounted in.

It is a parameter because the metadata document's URL is not free: RFC 8414 §3 inserts the
well-known suffix ahead of an issuer's path, so an issuer with a path is discovered at a URL a
client reaches only by constructing it, while a deployment serving one tenant at the origin wants
the URL every client tries first.

Whichever is chosen, the `OAuthConfig` has to agree, which is what `OAuthConfig.standard` and
`OAuthConfig.atOrigin` are for. A disagreement is silent: everything works except discovery.
-/
inductive Mount where
  /-- Below each tenant's own path, beside the sign-in routes and where `OAuthConfig.standard`
  puts them. The metadata document answers at the well-known suffix followed by `/t/<tenant>`. -/
  | perTenant
  /-- At the origin, for a deployment serving one tenant, where `OAuthConfig.atOrigin` puts them.
  The tenant is named here because there is no longer a path to read it from. -/
  | origin (tenant : TenantId)

/-! ## Configuration -/

structure Config where
  ports : OAuth.Service.Ports IO
  /-- The same lookup `Authentication.Http.Config.tenant` takes, and in a deployment serving both
  it is the same value. A tenant it does not recognise is a 404 here too. -/
  tenant : (t : TenantId) → IO (Option (TenantConfig t))
  /-- The second lookup, which the sign-in routes have no field for: an issuer, its endpoints and
  its lifetimes are not derivable from a `TenantConfig`. -/
  oauth : (t : TenantId) → IO (Option (OAuthConfig t))
  pages : OAuthPages := .standard
  mountedAt : Mount := .perTenant
  /-- What a request naming no `scope` at all is asked about.

  OAuth 2.1 §3.2.2.1 leaves a server two answers to such a request, a default set or a refusal.
  Unset is the refusal. It is unset rather than defaulted to `scopesSupported`, because those are
  two different statements: what this deployment can grant, and what it is willing to offer
  somebody who asked for nothing. The page asks either way, and a box left unticked is a scope
  withheld. -/
  defaultScopes : Option (List Scope) := none
  /-- The field the consent form's anti-forgery token rides in. It has to match the
  `paramName` of whatever `Middleware.antiForgery` wraps these routes; this is that
  middleware's own default. -/
  antiForgeryField : String := "__anti-forgery-token"
  /-- Where a request that needs somebody signed in is sent, which is the one decision here that
  is not the protocol's. The default is this library's own sign-in route, carrying the
  authorization request as its `returnTo`, so the person lands back on it. That needs the
  authorization endpoint's path in the tenant's `returnToAllowlist`; without it the sign-in lands
  on the tenant's default and the client is left waiting. -/
  signIn : (t : TenantId) → (returnTo : String) → String := fun t target =>
    BaseUrl.tenantPath t ++ "/signin?returnTo=" ++ Uri.encodeComponent target
  /-- Answered for a tenant neither lookup recognises. A page rather than a bare status, because
  it has to be indistinguishable from a path nothing routes. -/
  notFound : String := _root_.Authentication.Http.Pages.standard.unknown

/-! ## Reading the request -/

private def contentTypeIs (request : Request Body.Stream) (media : String) : Bool :=
  match request.line.headers.get? Header.Name.contentType with
  | some value => value.value.trimAscii.toString.toLower.startsWith media
  | none => false

/-- The form body, or `none` where the request did not declare one. The token endpoint reads a
form and the registration endpoint reads JSON, and neither reads the other: a parser accepting
either would accept a form-encoded registration, which this server has agreed to read no such
thing of. -/
private def formParams (request : Request Body.Stream) : ContextAsync (Option Params) := do
  if contentTypeIs request "application/x-www-form-urlencoded" then
    let body ← request.body.readAll (α := String)
    pure (some (Params.ofQuery (Middleware.ContentType.FormUrlEncoded.parse body)))
  else pure none

private def queryParams (request : Request Body.Stream) : Params :=
  Params.ofQuery request.line.uri.query

/-- What a form said under one name, and nothing at all where it said it twice: a duplicated
answer is not one, and every field read here fails closed. -/
private def only (params : Params) (name : String) : Option String :=
  (params.single? name).toOption.bind id

/-- The session credential the browser presented, which `authorize` is what decides the meaning
of. Read from the cookie the sign-in flow issued and from nowhere else. -/
private def presentedSession (request : Request Body.Stream) : Option CredentialValue :=
  (_root_.Authentication.Http.cookieNamed request "auth_session").map fun value => ⟨value⟩

/-! ## Writing the response -/

private def headerValue (text : String) : Header.Value :=
  (Header.Value.ofString? text).getD default

/--
Every response these routes produce. `no-store` is OAuth 2.1 §3.2.3 and is why this exists: an
authorization response carries a code in its `Location`, a token response carries the token
itself, and a consent page names an account. The framing and sniffing headers are here for the
reason the sign-in routes carry them, and a consent page is the one page on this server where
being framed would turn somebody's click into a grant.
-/
private def guarded (response : Response Body.Any) (location : Option String) :
    Response Body.Any :=
  let headers := response.line.headers
    |>.insert (Header.Name.mk "x-frame-options") (headerValue "DENY")
    |>.insert (Header.Name.mk "x-content-type-options") (headerValue "nosniff")
    |>.insert (Header.Name.mk "referrer-policy") (headerValue "no-referrer")
    |>.insert (Header.Name.mk "cache-control") (headerValue "no-store")
  let headers := match location with
    | none => headers
    | some target =>
      headers.insert (Header.Name.mk "location")
        (headerValue
          (String.ofList (_root_.Authentication.Http.escapeLocation target.toUTF8.toList)))
  { response with line := { response.line with headers } }

private def htmlPage (status : Status) (body : String) : ContextAsync (Response Body.Any) := do
  let response ← Response.withStatus status |>.html body
  pure (guarded response none)

private def jsonBody (status : Status) (payload : Json) : ContextAsync (Response Body.Any) := do
  let response ← Response.withStatus status |>.json payload.compress
  pure (guarded response none)

private def redirectTo (status : Status) (target : String) : ContextAsync (Response Body.Any) := do
  let response ← Response.withStatus status |>.html ""
  pure (guarded response (some target))

private def statusOfCode : Nat → Status
  | 401 => .unauthorized
  | 403 => .forbidden
  | 500 => .internalServerError
  | 503 => .serviceUnavailable
  | _ => .badRequest

/-- A rejection the client is entitled to read, as the JSON body of RFC 6749 §5.2. -/
private def errorBody (error : ErrorResponse) : ContextAsync (Response Body.Any) :=
  jsonBody (statusOfCode error.status) error.toJson

/-! ## The token the consent form carries -/

/--
Which token the consent form carries, and who checks it.

Where `Middleware.antiForgery` wraps these routes it has already established a token and answered
whatever did not carry one, so the page renders that middleware's field and nothing more is
checked here. Where it does not, the token is derived from the session cookie under the current
pepper, exactly as the sign-in routes derive theirs from the attempt cookie, and it is checked
here.

A consent form has to be unpostable from another site either way. What it grants is an access
token, and a deployment that mounted these bare would otherwise be one where any page on the
internet can silently grant scopes to a client of its own.
-/
private inductive Guard where
  | middleware (token : String)
  | derived (token : String)

private def guardOf (config : Config) (request : Request Body.Stream)
    (session : Option CredentialValue) : Guard :=
  match request.extensions.get Middleware.AntiForgeryToken with
  | some established => .middleware established.value
  | none =>
    .derived (Codec.Base64Url.encodeString
      (config.ports.peppers.current.derive "oauth-consent" (session.getD ⟨""⟩)))

private def Guard.token : Guard → String
  | .middleware value | .derived value => value

private def Guard.accepts : Guard → Option String → Bool
  | .middleware _, _ => true
  | .derived _, none => false
  | .derived expected, some offered => Crypto.bytesEqual offered.toUTF8 expected.toUTF8

/-! ## Handlers -/

private def notFoundPage (config : Config) : ContextAsync (Response Body.Any) :=
  htmlPage .notFound config.notFound

/-- Resolves both of the tenant's configurations, or answers the way an unrouted path would. -/
private def withTenant (config : Config) (raw : String)
    (body : (t : TenantId) → TenantConfig t → OAuthConfig t → ContextAsync (Response Body.Any)) :
    ContextAsync (Response Body.Any) := do
  let tenant : TenantId := ⟨raw⟩
  match ← (config.tenant tenant : IO _) with
  | none => notFoundPage config
  | some tenantConfig =>
    match ← (config.oauth tenant : IO _) with
    | none => notFoundPage config
    | some oauthConfig => body tenant tenantConfig oauthConfig

/-- Applied wherever a prompt is built, so that what the `POST` reads an answer about is what the
`GET` displayed. -/
private def amended {tenant : TenantId} (config : Config)
    (prompt : Service.ConsentPrompt tenant) : Service.ConsentPrompt tenant :=
  match config.defaultScopes with
  | none => prompt
  | some scopes => prompt.withDefaultScopes scopes

private def consentPage {tenant : TenantId} (config : Config) (tenantConfig : TenantConfig tenant)
    (action : String) (guard : Guard) (prompt : Service.ConsentPrompt tenant) :
    ContextAsync (Response Body.Any) :=
  htmlPage .ok
    (config.pages.consent
      { tenantName := tenantConfig.displayName
        action
        antiForgeryField := config.antiForgeryField
        antiForgeryToken := guard.token
        clientName := prompt.client.metadata.clientName
        clientHost := prompt.clientHost
        redirectHost := prompt.redirectHost
        loopbackOnly := prompt.loopbackOnly
        resource := prompt.resource
        requestedScopes := prompt.requestedScopes
        grantedScopes := prompt.grantedScopes })

/-- What an outcome becomes. `redirect` is `302` where a `GET` asked and `303` where a `POST` did,
so that the answer to a form is not a target the browser would post to again. -/
private def answered {tenant : TenantId} (config : Config) (redirect : Status) (target : String)
    (onConsent : Service.ConsentPrompt tenant → ContextAsync (Response Body.Any)) :
    Service.Outcome tenant → ContextAsync (Response Body.Any)
  | .consent prompt => onConsent prompt
  | .respond destination => redirectTo redirect destination.location
  | .authenticate => redirectTo redirect (config.signIn tenant target)
  | .refuse error => htmlPage .badRequest (config.pages.refusedClient error.description)

private def authorizeGet [Clock IO] [RandomBytes IO] (config : Config) (raw : String) :
    Routing.Result := fun request =>
  withTenant config raw fun _ tenantConfig oauthConfig => do
    let target := toString request.line.uri
    let session := presentedSession request
    let guard := guardOf config request session
    answered config .found target
      (fun prompt => consentPage config tenantConfig target guard (amended config prompt))
      (← (Service.authorize config.ports oauthConfig (queryParams request) session : IO _))

/--
The answer to the consent page.

The request is read twice and the two readings are kept apart. The query is what `authorize` runs
on again, which is what makes the decision one about the request as it arrived rather than about
hidden fields a page carried back; the form body carries the answer alone, which is the one thing
the query cannot hold.
-/
private def authorizePost [Clock IO] [RandomBytes IO] (config : Config) (raw : String) :
    Routing.Result := fun request =>
  withTenant config raw fun _ tenantConfig oauthConfig => do
    let target := toString request.line.uri
    let session := presentedSession request
    let form := (← formParams request).getD []
    let guard := guardOf config request session
    if !guard.accepts (only form config.antiForgeryField) then
      htmlPage .forbidden config.notFound
    else
      let render (prompt : Service.ConsentPrompt _) :=
        consentPage config tenantConfig target guard prompt
      match ← (Service.authorize config.ports oauthConfig (queryParams request) session : IO _) with
      | .consent prompt =>
        let prompt := amended config prompt
        let ticked (field : String) : Bool := form.any fun (name, _) => name == field
        let decision : Service.ConsentDecision _ :=
          if ConsentForm.approved (only form ConsentForm.answerField) then
            .granted prompt (Scope.approved prompt.requestedScopes ticked)
          else .denied prompt
        answered config .seeOther target render
          (← (Service.conclude config.ports oauthConfig decision : IO _))
      | outcome => answered config .seeOther target (render <| amended config ·) outcome

/-- The token endpoint. Form encoded, read from the body alone: a token request that took a
parameter from the query string would be reading one the client did not agree to send there. -/
private def tokenEndpoint [Clock IO] [RandomBytes IO] (config : Config) (raw : String) :
    Routing.Result := fun request =>
  withTenant config raw fun _ _ oauthConfig => do
    match ← formParams request with
    | none =>
      errorBody
        { error := .invalidRequest
          description := "the token endpoint reads application/x-www-form-urlencoded" }
    | some params =>
      match ← (Service.token config.ports oauthConfig params : IO _) with
      | .error error => errorBody error
      | .ok response => jsonBody .ok response.toJson

/-- Registration, which is JSON (RFC 7591 §3.1). Nothing here reads a form, so a form-encoded
registration is refused for being unreadable rather than accepted for looking close enough. -/
private def registerEndpoint [Clock IO] [RandomBytes IO] (config : Config) (raw : String) :
    Routing.Result := fun request =>
  withTenant config raw fun tenant _ _ => do
    let body ← request.body.readAll (α := String)
    match Json.parse body with
    | .error _ =>
      errorBody { error := .invalidClientMetadata, description := "the request body is not JSON" }
    | .ok payload =>
      match ← (Service.register (tenant := tenant) config.ports payload : IO _) with
      | .error error => errorBody error
      | .ok record => jsonBody .created (Registration.response record)

private def metadataEndpoint (config : Config) (raw : String) : Routing.Result := fun _ =>
  withTenant config raw fun _ _ oauthConfig =>
    jsonBody .ok (metadataDocument config.ports.documents oauthConfig)

/-! ## The tables -/

route_table PerTenant [
  authorize := "/t/:tenant:String/oauth/authorize",
  token := "/t/:tenant:String/oauth/token",
  register := "/t/:tenant:String/oauth/register",
  metadata := "/.well-known/oauth-authorization-server/t/:tenant:String"
]

route_table AtOrigin [
  authorize := "/oauth/authorize",
  token := "/oauth/token",
  register := "/oauth/register",
  metadata := "/.well-known/oauth-authorization-server"
]

/--
The routes, split by what may wrap them, because mounting them as one list gets one half wrong.

`/oauth/authorize` is answered by a person in a browser and its `POST` must be unpostable from
another site. `/oauth/token` and `/oauth/register` are answered by a program carrying no cookie,
and anti-forgery middleware refuses those by design. An application wrapping the whole set
uniformly has either a consent form that cannot be posted or a token endpoint that refuses every
client.

Both lists carry complete paths for the chosen `Mount`. Neither may be mounted under a further
prefix: the metadata document advertises where they answer, and RFC 8414 fixes where the document
itself answers.
-/
structure Routes where
  /-- Mount inside `Middleware.session` and `Middleware.antiForgery`, or inside neither; see
  `Config.antiForgeryField`. -/
  browser : List (Routing.Route Routing.Result)
  /-- Mount outside `Middleware.antiForgery`. -/
  client : List (Routing.Route Routing.Result)

def routes [Clock IO] [RandomBytes IO] (config : Config) : Routes :=
  match config.mountedAt with
  | .perTenant =>
    { browser :=
        [ .get PerTenant.patterns.authorize (authorizeGet config),
          .post PerTenant.patterns.authorize (authorizePost config) ]
      client :=
        [ .post PerTenant.patterns.token (tokenEndpoint config),
          .post PerTenant.patterns.register (registerEndpoint config),
          .get PerTenant.patterns.metadata (metadataEndpoint config) ] }
  | .origin tenant =>
    { browser :=
        [ .get AtOrigin.patterns.authorize (authorizeGet config tenant.value),
          .post AtOrigin.patterns.authorize (authorizePost config tenant.value) ]
      client :=
        [ .post AtOrigin.patterns.token (tokenEndpoint config tenant.value),
          .post AtOrigin.patterns.register (registerEndpoint config tenant.value),
          .get AtOrigin.patterns.metadata (metadataEndpoint config tenant.value) ] }

/--
Both halves in one handler, for a deployment with no router of its own to mount them in.

`browser` is wrapped in whatever is passed and `client` is not, which is why this takes the
wrapper rather than being wrapped from outside: the same wrapper over both is the mistake
`Routes` exists to make hard. The default wraps in nothing, which is what a deployment relying on
the token derived from the session cookie wants.
-/
def handler [Clock IO] [RandomBytes IO] (config : Config)
    (browser : StatelessHandler → StatelessHandler := id) : StatelessHandler :=
  let split := routes config
  let wrapped := browser (Routing.toHandler split.browser (fun _ => notFoundPage config))
  Routing.toHandler split.client fun request =>
    -- Matched before the wrapper rather than inside it, so that a path neither table answers is
    -- a 404 rather than whatever the wrapper makes of it: anti-forgery middleware answers an
    -- unroutable `POST` with a 403, which says the path exists.
    if (Routing.matchTable split.browser request.line.method
        request.line.uri.path.toDecodedSegments.toList).isSome then
      wrapped.onRequest request
    else notFoundPage config

end Authentication.OAuth.Http
