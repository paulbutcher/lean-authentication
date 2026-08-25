/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import AuthenticationHttp.Pages
public import Routing
import Crypto.Compare
import Middleware

/-!
The sign-in routes (AUTH-13.2).

Only the sign-in routes. There is no route here that creates an invitation, revokes a session,
changes a policy or clears a suppression, and there cannot be: the library owns identity and
nothing about permissions, so it has no basis on which to decide who may call one. Those stay
plain service functions the client calls once it has decided (§13).

Two things the service cannot do on its own are done here, because both are properties of an
HTTP response and the service has none:

- The mechanical shape of the answer to a sign-in request is equalised (AUTH-14.2.4). Every
  outcome leaves with the same status, the same headers, and one `Set-Cookie`, which means the
  refusals set a cookie too. The service already equalised the time.
- The redirect target is validated against the tenant's allowlist before anything is sent to it
  (AUTH-9.8).
-/

public section

namespace Authentication.Http

open Std Http
open Std.Async
open Std.Http.Server
open Authentication.Service

/-! ## Configuration -/

structure Config where
  ports : Ports IO
  /-- The client's own lookup. A tenant it does not recognise is a 404, decided by the client
  because the library holds nothing about a tenant beyond its identifier (AUTH-4.1.3). -/
  tenant : (t : TenantId) → IO (Option (TenantConfig t))
  pages : Pages := .standard
  /-- The form field a bot-mitigation challenge writes its answer into, if one is configured
  (AUTH-14.1.8). The name is the provider's (`cf-turnstile-response`, `h-captcha-response`,
  `g-recaptcha-response`), which is why it is a setting and not a constant. Leaving it unset
  reads no field, which is right only alongside the default `HumanCheck` that admits everyone.
  The field itself belongs to whatever the client's page put in the form. -/
  humanProofField : Option String := none
  /-- Provider callbacks, each answering on `/t/<tenant>/webhooks/<name>` (AUTH-12.1.1). Empty
  unless configured, because an endpoint that accepts delivery events without being able to
  establish who sent them is worse than no endpoint. Each one verifies before it returns
  anything, so nothing here decides whether to trust a payload; it decides only where to route
  one. -/
  webhooks : List (WebhookEndpoint IO) := []

/-! ## Reading the request -/

private def formBody (request : Request Body.Stream) : ContextAsync URI.Query := do
  let declared :=
    match request.line.headers.get? Header.Name.contentType with
    | some value =>
      value.value.trimAscii.toString.toLower.startsWith "application/x-www-form-urlencoded"
    | none => false
  if declared then
    pure (Middleware.ContentType.FormUrlEncoded.parse (← request.body.readAll (α := String)))
  else pure .empty

private def queryOf (request : Request Body.Stream) : URI.Query := request.line.uri.query

private def cookieNamed (request : Request Body.Stream) (name : String) : Option String :=
  match request.line.headers.get? Middleware.Header.Name.cookie with
  | none => none
  | some value => (Middleware.parseCookieHeader value.value).lookup name

/--
What the request says about whoever made it. The address is taken from the `ForwardedFor`
extension a client installs `Middleware.forwardedRemoteAddr` to establish, and from nowhere
else: reading `X-Forwarded-For` here unconditionally would hand the source-address rate limit
scope (AUTH-14.1.1) to anyone willing to set a header. Its absence is a proxy that did not say,
which the limiter already treats as a request that still counts against every other scope.
-/
private def requesterOf (request : Request Body.Stream) : RequestContext :=
  { ip := (request.extensions.get Middleware.ForwardedFor).map (·.addr)
    userAgent := (request.line.headers.get? (Header.Name.mk "user-agent")).map (·.value) }

/-! ## Writing the response -/

private def headerValue (text : String) : Header.Value :=
  (Header.Value.ofString? text).getD default

private def setCookieName : Header.Name := Middleware.Header.Name.setCookie

/-- The attributes are the `CookieSpec`'s, which the core fixed and no caller can weaken
(AUTH-9.2). The lifetime travels as `Max-Age` rather than `Expires` so that nothing here depends
on a date format. -/
private def setCookie (now : Timestamp) (spec : CookieSpec) : Header.Value :=
  (Middleware.SetCookie.serialize
    { name := spec.name
      value := spec.value
      attrs :=
        { path := some spec.path
          maxAge := some (spec.expiresAt.epochSeconds - now.epochSeconds)
          secure := spec.secure
          httpOnly := spec.httpOnly
          sameSite := some (match spec.sameSite with
            | .lax => .lax
            | .strict => .strict
            | .none => .none) } }).2

private def clearCookie (base : BaseUrl) (name : String) (path : String) : Header.Value :=
  (Middleware.SetCookie.serialize
    { name
      value := ""
      attrs :=
        { path := some path
          maxAge := some 0
          httpOnly := true
          secure := base.secureCookies } }).2

/--
Every response these routes produce, so that the header set does not vary with the outcome and
an authentication page is never framed (AUTH-14.1.5, AUTH-14.2.4). `no-store` is here because a
page showing a verification code has no business in a shared cache or a back button.
-/
private def finish (status : Status) (body : String) (cookies : List Header.Value)
    (location : Option String := none) : ContextAsync (Response Body.Any) := do
  let response ← Response.withStatus status |>.html body
  let headers := response.line.headers
    |>.insert (Header.Name.mk "x-frame-options") (headerValue "DENY")
    |>.insert (Header.Name.mk "x-content-type-options") (headerValue "nosniff")
    |>.insert (Header.Name.mk "referrer-policy") (headerValue "no-referrer")
    |>.insert (Header.Name.mk "cache-control") (headerValue "no-store")
  let headers := cookies.foldl (fun hs value => hs.insert setCookieName value) headers
  let headers := match location with
    | none => headers
    | some target => headers.insert (Header.Name.mk "location") (headerValue target)
  pure { response with line := { response.line with headers } }

/-! ## The attempt cookie, and the token bound to it -/

/--
What the attempt cookie carries. The redirect target rides here because the magic link carries
the attempt and its token and nothing else: the browser that opens the link has no other way to
say where the person was going, and this cookie is present on exactly the requests that can
confirm a sign-in from that browser (AUTH-9.8).
-/
structure AttemptCookie (tenant : TenantId) where
  attempt : AttemptId tenant
  nonce : CredentialValue
  returnTo : Option String := none
  deriving DecidableEq, Repr

namespace AttemptCookie

/-- Bytes rather than characters, because what has to stay inside the browser's limit is the
cookie, and a character is up to four of them. A `Set-Cookie` past that limit is discarded in
silence, and the cookie discarded would be the one the flow depends on, so a target longer than
this is left behind and the sign-in lands on the tenant's default rather than nowhere. -/
def returnToLimit : Nat := 1024

/-- Base64url, so the field carries no `:` to confuse the split and nothing a cookie value may
not hold. -/
def encodeReturnTo (target : String) : Option String :=
  if target.utf8ByteSize > returnToLimit then none
  else some (Codec.Base64Url.encodeString target.toUTF8)

def decodeReturnTo (field : String) : Option String :=
  (Codec.Base64Url.decodeString field).bind String.fromUTF8?

/-- Appends the target to the two fields the core wrote (`Attempt.cookieValue`). -/
def withReturnTo (value : String) (target : Option String) : String :=
  match target.bind encodeReturnTo with
  | none => value
  | some encoded => value ++ ":" ++ encoded

/-- Two fields are a cookie issued before targets rode in one, and the browser holding it must
still be able to finish signing in. -/
def parse {tenant : TenantId} (value : String) : Option (AttemptCookie tenant) :=
  match (value.toList.splitOn ':').map String.ofList with
  | [attempt, nonce] => some { attempt := ⟨attempt⟩, nonce := ⟨nonce⟩ }
  | [attempt, nonce, target] =>
    some { attempt := ⟨attempt⟩, nonce := ⟨nonce⟩, returnTo := decodeReturnTo target }
  | _ => none

end AttemptCookie

/--
The anti-forgery token (AUTH-14.1.4). Derived from the binding nonce in the attempt cookie under
the current pepper, so it is bound to that cookie by construction rather than by a second record
somebody has to keep: a form posted from another origin cannot carry the right one, because the
origin that would have to read the cookie cannot.
-/
private def formToken (peppers : PepperRing) (nonce : CredentialValue) : String :=
  Codec.Base64Url.encodeString (peppers.current.derive "form-token" nonce)

private def tokenAccepted (peppers : PepperRing) (nonce : CredentialValue)
    (offered : Option String) : Bool :=
  match offered with
  | none => false
  | some offered => Crypto.bytesEqual offered.toUTF8 (formToken peppers nonce).toUTF8

/-! ## Handlers -/

private def notFoundPage (config : Config) : ContextAsync (Response Body.Any) :=
  finish .notFound config.pages.unknown []

private def signInPath (tenant : TenantId) : String :=
  BaseUrl.tenantPath tenant ++ "/signin"

private def codePath (tenant : TenantId) : String :=
  BaseUrl.tenantPath tenant ++ "/signin/code"

private def emailedCodePath (tenant : TenantId) : String :=
  BaseUrl.tenantPath tenant ++ "/signin/emailed-code"

private def confirmPath (tenant : TenantId) : String :=
  BaseUrl.tenantPath tenant ++ "/signin/confirm"

/-- Offered only where the tenant puts a code in the mail (AUTH-5.4.1). Offering it regardless
would give the page a field for a code that is never sent. -/
private def emailedCodeAction {tenant : TenantId} (config : TenantConfig tenant) : Option String :=
  if config.emailedCodeEnabled then some (emailedCodePath tenant) else none

/-- Resolves the tenant, or answers the way an unrouted path would. A tenant the client does not
recognise must be indistinguishable from one that does not exist. -/
private def withTenant (config : Config) (raw : String)
    (body : (t : TenantId) → TenantConfig t → ContextAsync (Response Body.Any)) :
    ContextAsync (Response Body.Any) := do
  let tenant : TenantId := ⟨raw⟩
  match ← (config.tenant tenant : IO _) with
  | none => notFoundPage config
  | some tenantConfig => body tenant tenantConfig

private def signInForm (config : Config) (raw : String) : Routing.Result := fun request =>
  withTenant config raw fun tenant tenantConfig => do
    finish .ok
      (config.pages.signIn
        { tenantName := tenantConfig.displayName
          action := signInPath tenant
          returnTo := (queryOf request).get "returnTo" })
      []

/--
Beginning a sign-in. Every path out of here answers `200`, with the same headers and exactly one
`Set-Cookie`, whatever happened (AUTH-14.2.4).

That last part is why a refusal sets a cookie at all. `begin` produces no attempt for an address
it will not send to, so there is no cookie to set and the missing header would say so; the
decoy is drawn the same way a real one is and is the same shape, and a code typed against it
fails the way a code typed against an expired attempt fails. The redirect target is appended to
both for the same reason: a decoy shorter by the length of an encoded target would say which
was which.
-/
private def beginSignIn [Clock IO] [RandomBytes IO] (config : Config) (raw : String) : Routing.Result := fun request =>
  withTenant config raw fun tenant tenantConfig => do
    let form ← formBody request
    let returnTo := (form.get "returnTo").orElse fun _ => (queryOf request).get "returnTo"
    let requester := requesterOf request
    let now ← (Clock.now : IO Timestamp)
    let (outcome, response) ← (do
      match EmailAddress.parse ((form.get "email").getD "") with
      | .error _ =>
        -- The address never reaches `begin`, which takes a parsed one. It is still the policy
        -- that decides what is said, so that a client which chose silence keeps it.
        let response ← config.ports.responsePolicy.respond tenant .malformedAddress
        pure (({} : Outcome tenant), response)
      | .ok address =>
        Service.begin config.ports tenantConfig address requester
          (config.humanProofField.bind form.get) : IO _)
    let cookie ← match outcome.setCookies.head? with
      | some spec => pure spec
      | none => (do
        let attempt ← RandomBytes.draw 12
        let nonce ← RandomBytes.draw 16
        let value := match attempt, nonce with
          | .ok attempt, .ok nonce =>
            Codec.Base64Url.encodeString attempt ++ ":" ++ Codec.Base64Url.encodeString nonce
          | _, _ => ":"
        pure (CookieSpec.forAttempt tenantConfig.baseUrl tenant value
          (now.advance tenantConfig.attemptLifetime.duration)) : IO _)
    let cookie := { cookie with value := AttemptCookie.withReturnTo cookie.value returnTo }
    let token := (AttemptCookie.parse (tenant := tenant) cookie.value).map fun held =>
      formToken config.ports.peppers held.nonce
    finish .ok
      (config.pages.sent
        { tenantName := tenantConfig.displayName
          action := codePath tenant
          token
          returnTo
          emailedCodeAction := emailedCodeAction tenantConfig }
        response.message)
      [setCookie now cookie]

/-- Opening the magic link: a `GET` that issues nothing and consumes nothing (AUTH-5.2.1). The
code the cross-device page shows is derived from the token the link carried, which is why it can
be shown again without ever having been stored (AUTH-5.2.2). -/
private def openLink [Clock IO] [RandomBytes IO] (config : Config) (raw : String) : Routing.Result := fun request =>
  withTenant config raw fun tenant tenantConfig => do
    let query := queryOf request
    let attempt : AttemptId tenant := ⟨(query.get "attempt").getD ""⟩
    let token : CredentialValue := ⟨(query.get "token").getD ""⟩
    let held := (cookieNamed request "auth_attempt").bind (AttemptCookie.parse (tenant := tenant))
    match ← (Service.openLink config.ports tenantConfig attempt token
        (held.map (·.nonce)) : IO _) with
    | .error _ => notFoundPage config
    | .ok outcome =>
      let context : PageContext :=
        { tenantName := tenantConfig.displayName
          action := confirmPath tenant
          token := held.map fun cookie => formToken config.ports.peppers cookie.nonce
          returnTo := held.bind (·.returnTo) }
      if outcome.views.contains .confirmSignIn then
        finish .ok (config.pages.confirm context) []
      else if outcome.views.contains .showVerificationCode then
        finish .ok
          (config.pages.code context (displayCode (revealedCode config.ports.peppers token))) []
      else notFoundPage config

/-- What a completed attempt turns into: the session cookie the service built, the attempt
cookie cleared, and a redirect to a target the tenant allowed (AUTH-9.8). -/
private def settled (config : Config) (tenant : TenantId) (tenantConfig : TenantConfig tenant)
    (now : Timestamp) (outcome : Outcome tenant) (returnTo : Option String)
    (context : PageContext) : ContextAsync (Response Body.Any) :=
  match outcome.session with
  | some _ =>
    finish .seeOther ""
      (outcome.setCookies.map (setCookie now)
        ++ outcome.clearCookies.map fun (name, path) => clearCookie tenantConfig.baseUrl name path)
      (some (tenantConfig.returnTo returnTo))
  | none =>
    match outcome.refused with
    | some reason => finish .ok (config.pages.refused context reason) []
    | none =>
      match outcome.views.filterMap (fun view =>
        match view with | .codeRejected remaining => some remaining | _ => none) with
      | remaining :: _ => finish .ok (config.pages.codeRejected context remaining) []
      | [] => notFoundPage config

/-- The same-device `POST` (AUTH-5.2.1). The attempt comes from the cookie rather than the form,
so a request that does not hold the cookie has no attempt to name. -/
private def confirmSignIn [Clock IO] [RandomBytes IO] (config : Config) (raw : String) : Routing.Result := fun request =>
  withTenant config raw fun tenant tenantConfig => do
    let form ← formBody request
    match (cookieNamed request "auth_attempt").bind (AttemptCookie.parse (tenant := tenant)) with
    | none => notFoundPage config
    | some ⟨attempt, nonce, carried⟩ =>
      if !tokenAccepted config.ports.peppers nonce (form.get "token") then
        finish .forbidden config.pages.unknown []
      else
        let now ← (Clock.now : IO Timestamp)
        match ← (Service.confirmSignIn config.ports tenantConfig attempt nonce : IO _) with
        | .error _ => notFoundPage config
        | .ok outcome =>
          -- The form first, so a client whose confirm page renders `context.returnTo` is
          -- believed; the cookie behind it, so one that ignores it still lands where the
          -- person asked, which is the whole of what the cookie carries the target for.
          let returnTo := (form.get "returnTo").orElse fun _ => carried
          settled config tenant tenantConfig now outcome returnTo
            { tenantName := tenantConfig.displayName
              action := confirmPath tenant
              token := some (formToken config.ports.peppers nonce)
              returnTo }

/-- The code typed back into the browser the flow began in. -/
private def submitCode [Clock IO] [RandomBytes IO] (config : Config) (raw : String) : Routing.Result := fun request =>
  withTenant config raw fun tenant tenantConfig => do
    let form ← formBody request
    match (cookieNamed request "auth_attempt").bind (AttemptCookie.parse (tenant := tenant)) with
    | none => notFoundPage config
    | some ⟨attempt, nonce, carried⟩ =>
      if !tokenAccepted config.ports.peppers nonce (form.get "token") then
        finish .forbidden config.pages.unknown []
      else
        let now ← (Clock.now : IO Timestamp)
        let returnTo := (form.get "returnTo").orElse fun _ => carried
        let typed := (form.get "code").getD ""
        let requester := requesterOf request
        let context : PageContext :=
          { tenantName := tenantConfig.displayName
            action := codePath tenant
            token := some (formToken config.ports.peppers nonce)
            returnTo
            emailedCodeAction := emailedCodeAction tenantConfig }
        match ← (Service.submitCode config.ports tenantConfig attempt typed nonce requester :
            IO _) with
        | .error _ => finish .ok (config.pages.codeRejected context 0) []
        | .ok outcome => settled config tenant tenantConfig now outcome returnTo context

/-- The optional code carried in the mail body (AUTH-5.4). It is a separate endpoint from the
revealed code because they are separate credentials sharing one entry budget: an endpoint that
tried both would spend two entries on one submission. -/
private def submitEmailedCode [Clock IO] [RandomBytes IO] (config : Config) (raw : String) : Routing.Result := fun request =>
  withTenant config raw fun tenant tenantConfig => do
    let form ← formBody request
    match (cookieNamed request "auth_attempt").bind (AttemptCookie.parse (tenant := tenant)) with
    | none => notFoundPage config
    | some ⟨attempt, nonce, carried⟩ =>
      if !tokenAccepted config.ports.peppers nonce (form.get "token") then
        finish .forbidden config.pages.unknown []
      else
        let now ← (Clock.now : IO Timestamp)
        let returnTo := (form.get "returnTo").orElse fun _ => carried
        let typed := (form.get "code").getD ""
        let requester := requesterOf request
        let context : PageContext :=
          { tenantName := tenantConfig.displayName
            action := codePath tenant
            token := some (formToken config.ports.peppers nonce)
            returnTo
            emailedCodeAction := emailedCodeAction tenantConfig }
        match ← (Service.submitEmailedCode config.ports tenantConfig attempt typed nonce
            requester : IO _) with
        | .error _ => finish .ok (config.pages.codeRejected context 0) []
        | .ok outcome => settled config tenant tenantConfig now outcome returnTo context

/-- Accepting an invitation begins an attempt for the invited address and runs the whole of §5,
so a link opened on a phone signs nobody in on that phone (AUTH-8.4). -/
private def acceptInvitation [Clock IO] [RandomBytes IO] (config : Config) (raw : String) : Routing.Result := fun request =>
  withTenant config raw fun tenant tenantConfig => do
    let query := queryOf request
    let invitation : InvitationId tenant := ⟨(query.get "invitation").getD ""⟩
    let token : CredentialValue := ⟨(query.get "token").getD ""⟩
    let now ← (Clock.now : IO Timestamp)
    match ← (Service.acceptInvitation config.ports tenantConfig invitation token
        (requesterOf request) : IO _) with
    | .error _ => notFoundPage config
    | .ok outcome =>
      let cookie := outcome.setCookies.head?
      let token := (cookie.bind fun spec => AttemptCookie.parse (tenant := tenant) spec.value).map
        fun held => formToken config.ports.peppers held.nonce
      finish .ok
        (config.pages.sent
          { tenantName := tenantConfig.displayName, action := codePath tenant, token
            emailedCodeAction := emailedCodeAction tenantConfig }
          .checkYourMail)
        (cookie.toList.map (setCookie now))

/--
A provider posting a delivery event. Not an administrative route, which AUTH-13.2 forbids here:
the decision it carries out is the provider's report that an address bounced, not a client's
decision about who may do what, and there is no caller to authorise. Clearing a suppression, the
operation AUTH-13.2 does name, has no route and will not get one.

The endpoint verifies before it returns anything, so this reads no header and trusts no field. It
answers `200` on anything it accepted and `403` on anything it did not, which is what a provider
needs to decide whether to retry.
-/
private def webhook [Clock IO] (config : Config) (rawTenant : String) (name : String) :
    Routing.Result := fun request =>
  withTenant config rawTenant fun tenant _ => do
    match config.webhooks.find? (·.name == name) with
    | none => notFoundPage config
    | some endpoint =>
      let body ← request.body.readAll (α := String)
      let header (field : String) : Option String :=
        (Header.Name.ofString? field.toLower).bind fun name =>
          (request.line.headers.get? name).map (·.value)
      match ← (endpoint.accept tenant header body : IO _) with
      | .rejected => finish .forbidden "" []
      | .accepted => finish .ok "" []
      | .ingest events => do
        for event in events do
          let _ ← (ingestDelivery (tenant := tenant) config.ports event : IO _)
        finish .ok "" []

/-! ## The table -/

route_table SignIn [
  form := "/t/:tenant:String/signin",
  link := "/t/:tenant:String/signin/link",
  confirm := "/t/:tenant:String/signin/confirm",
  code := "/t/:tenant:String/signin/code",
  emailedCode := "/t/:tenant:String/signin/emailed-code",
  accept := "/t/:tenant:String/invitation/accept",
  webhook := "/t/:tenant:String/webhooks/:provider:String"
]

/-- The paths are the ones `BaseUrl.url` builds, because the mail has to arrive somewhere these
routes answer (AUTH-4.3.2). -/
def routes [Clock IO] [RandomBytes IO] (config : Config) : List (Routing.Route Routing.Result) :=
  [ .get SignIn.patterns.form (signInForm config),
    .post SignIn.patterns.form (beginSignIn config),
    .get SignIn.patterns.link (openLink config),
    .post SignIn.patterns.confirm (confirmSignIn config),
    .post SignIn.patterns.code (submitCode config),
    .post SignIn.patterns.emailedCode (submitEmailedCode config),
    .get SignIn.patterns.accept (acceptInvitation config),
    .post SignIn.patterns.webhook (webhook config) ]

/-- Mount this wherever the application's own router is. Nothing here is a `Middleware`: these
are routes, and what wraps them is the client's. -/
def handler [Clock IO] [RandomBytes IO] (config : Config) : StatelessHandler :=
  Routing.toHandler (routes config) (fun _ => notFoundPage config)

end Authentication.Http
