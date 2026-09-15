/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import AuthenticationHttp
public import AuthenticationOidc
public import Routing
import Middleware

/-!
The federated sign-in routes (§6).

They are not in `AuthenticationHttp` beside the magic link ones, and that is AUTH-6.11: this
target reaches OpenSSL through `AuthenticationOidc`, and `AuthenticationHttp` is what a client
taking only the magic link flow mounts. It does depend on that target, for the response shape
every route in this library shares.
-/

public section

namespace Authentication.OidcHttp

open Std Http
open Std.Async
open Std.Http.Server
open Authentication.Http
open Authentication.Oidc

/--
Why a federated sign-in refused, for the operator rather than for the browser.

The page is the same whichever of these it was, and deliberately (AUTH-14.2.4), so this is the
only place the answer survives. Every case is a refusal the browser is told nothing about: a
provider the deployment has misconfigured and a provider having a bad afternoon reach the page
identically, and only the name here tells them apart.
-/
inductive Refusal where
  /-- Discovery, the token exchange, the ID token, or the invitation the sign-in was accepting. -/
  | protocol (error : OidcError)
  /-- The callback carried no `code`: a person who declined at the provider, or a request to
  this path that is not a callback at all. -/
  | noCode
  /-- The flow completed and issued no session. The reason is absent when nothing refused it,
  which is a session that could not be made rather than a person who was turned away. -/
  | noSession (reason : Option SignInRefusal)
  /-- The flow was adding a provider to an account and the credential was not written. -/
  | linkRefused (reason : Service.LinkFailure)
  /-- The sign-in was never begun, so the browser was not sent to the provider at all. -/
  | notStarted (reason : StartRefusal)
  /-- A link start arrived carrying no session cookie, which is also what a cross-site `POST`
  looks like (AUTH-6.7.1). -/
  | noSessionCookie
  /-- A link start carried a session cookie that named nobody. -/
  | sessionRejected (reason : SessionRejection)
  deriving Repr

/-- The operator's name for one, for a log record or a span attribute. Each case defers to the
name its own reason already carries, so a query over both sign-in routes groups on one set. -/
def Refusal.name : Refusal → String
  | .protocol error => error.name
  | .noCode => "no-code"
  | .noSession (some reason) => reason.name
  | .noSession none => "session-not-issued"
  | .linkRefused reason => reason.name
  | .notStarted reason => reason.name
  | .noSessionCookie => "no-session-cookie"
  | .sessionRejected reason => reason.name

structure Config where
  ports : Service.Ports IO
  oidc : SignInPorts IO
  /-- The client's own lookup, as the sign-in routes take (AUTH-4.1.3). -/
  tenant : (t : TenantId) → IO (Option (TenantConfig t))
  /-- What a refusal renders as. The default says nothing about which of the refusals it was,
  which is the enumeration-resistant choice AUTH-14.2.3 makes elsewhere. -/
  refusedPage : String := "<!doctype html><title>Sign-in failed</title><p>That sign-in could not be completed.</p>"
  /-- Where that refusal goes for the operator, since the page will not carry it
  (AUTH-14.2.6). The default does nothing, which is the only default that can be right: a
  library that chose a log format would be choosing it for every client. -/
  observeRefusal : TenantId → ProviderId → Refusal → IO Unit := fun _ _ _ => pure ()
  notFoundPage : String := "<!doctype html><title>Not found</title>"

/-- Where the provider sends the browser back. Built from the tenant's base URL, so it is the
same string a deployment registers with the provider and the same one the token request repeats
(AUTH-4.3.4). -/
def callbackUri {tenant : TenantId} (config : TenantConfig tenant) (provider : ProviderId) :
    String :=
  (config.baseUrl.url tenant ("/federated/" ++ provider.value ++ "/callback")).value

private def notFound (config : Config) : ContextAsync (Response Body.Any) :=
  finish .notFound config.notFoundPage []

/-- The one page every refusal renders, and the reason for it where somebody can read it. -/
private def refusedBecause (config : Config) (tenant : TenantId) (provider : ProviderConfig)
    (reason : Refusal) (cookies : List Header.Value := []) :
    ContextAsync (Response Body.Any) := do
  _ ← (config.observeRefusal tenant provider.id reason : IO Unit)
  finish .ok config.refusedPage cookies

private def withProvider (config : Config) (rawTenant rawProvider : String)
    (body : (t : TenantId) → TenantConfig t → ProviderConfig →
      ContextAsync (Response Body.Any)) : ContextAsync (Response Body.Any) := do
  let tenant : TenantId := ⟨rawTenant⟩
  match ← (config.tenant tenant : IO _) with
  | none => notFound config
  | some tenantConfig =>
    match tenantConfig.providers.find? (·.id.value == rawProvider) with
    | none => notFound config
    | some provider => body tenant tenantConfig provider

/-- Everything both starts do once they know which account, if any, the flow is for.

`303` rather than `302`, so that a `POST` becomes the `GET` the provider's authorization endpoint
expects rather than being replayed against it. -/
private def begin [Clock IO] [RandomBytes IO] {tenant : TenantId} (config : Config)
    (tenantConfig : TenantConfig tenant) (provider : ProviderConfig)
    (request : Request Body.Stream) (returnTo : Option String)
    (invitation : Option (InvitationId tenant)) (account : Option (AccountId tenant)) :
    ContextAsync (Response Body.Any) := do
  match ← (config.oidc.metadata.discover provider : IO _) with
  | .error reason => refusedBecause config tenant provider (.protocol reason)
  | .ok discovery =>
    match ← (beginFederated config.ports tenantConfig provider
        discovery (callbackUri tenantConfig provider.id) returnTo invitation account
        (requesterOf request) : IO _) with
    | .error reason => refusedBecause config tenant provider (.notStarted reason)
    | .ok begun =>
      let now ← (Clock.now : IO _)
      finish .seeOther "" [setCookie now begun.cookie] (some begun.authorizationUrl)

/-- Sends the browser to the provider, to sign in as whoever it answers with (AUTH-6.1). -/
private def start [Clock IO] [RandomBytes IO] (config : Config) (rawTenant rawProvider : String) :
    Routing.Result := fun request =>
  withProvider config rawTenant rawProvider fun _tenant tenantConfig provider =>
    begin config tenantConfig provider request (request.line.uri.query.get "returnTo")
      ((request.line.uri.query.get "invitation").map (⟨·⟩)) none

/--
Begins adding a provider to the account the request is already signed in as (AUTH-6.7.1).

A `POST`, and that is the whole of its forgery defence: the session cookie is `SameSite=Lax`,
which a cross-site `POST` does not carry, so a request provoked from anywhere but the
application's own pages arrives with no session and is refused here. It is also what makes the
intent explicit, as AUTH-6.7.1 requires: somebody signed in as one account may be starting a
sign-in as another, and a link has to be asked for rather than read into a session being present.

The account comes from that session and from nothing in the request, which is the rest of it. A
start that took an account identifier would link whoever asked to whichever account they named.
-/
private def linkStart [Clock IO] [RandomBytes IO] (config : Config)
    (rawTenant rawProvider : String) : Routing.Result := fun request =>
  withProvider config rawTenant rawProvider fun tenant tenantConfig provider => do
    let form ← formBody request
    match (cookieNamed request "auth_session").map (fun value => (⟨value⟩ : CredentialValue)) with
    | none => refusedBecause config tenant provider .noSessionCookie
    | some credential =>
      match ← (Service.identify config.ports tenantConfig credential : IO _) with
      | .error reason => refusedBecause config tenant provider (.sessionRejected reason)
      | .ok holder =>
        begin config tenantConfig provider request (form.get "returnTo") none (some holder.account)

/--
The provider's answer (AUTH-6.2, AUTH-6.5, AUTH-6.7).

Everything a refusal could report is answered with the same page, for the reason AUTH-14.2.4
equalises the other route's: which of the refusals it was describes the person rather than the
tenant, and this route has no way to ask what the client wanted said. What the browser is not
told, `Config.observeRefusal` is.
-/
private def complete [Clock IO] [RandomBytes IO] (config : Config)
    (rawTenant rawProvider : String) (fromBody : Bool) : Routing.Result := fun request =>
  withProvider config rawTenant rawProvider fun tenant tenantConfig provider => do
    let query ← if fromBody then formBody request else pure request.line.uri.query
    let held := cookieNamed request "auth_federation"
    let cleared := clearCookie tenantConfig.baseUrl "auth_federation" (BaseUrl.tenantPath tenant)
    match query.get "code" with
    | none => refusedBecause config tenant provider .noCode [cleared]
    | some code =>
      match ← (config.oidc.metadata.discover provider : IO _) with
      | .error reason => refusedBecause config tenant provider (.protocol reason) [cleared]
      | .ok discovery =>
        match ← (completeFederated config.ports config.oidc tenantConfig provider discovery
            (callbackUri tenantConfig provider.id) (query.get "state") held code
            (requesterOf request) (query.get "user") : IO _) with
        | .error reason => refusedBecause config tenant provider (.protocol reason) [cleared]
        | .ok completion =>
          let now ← (Clock.now : IO _)
          match completion.result with
          | .signedIn outcome =>
            let cookies := cleared :: outcome.setCookies.map (setCookie now)
            match outcome.session with
            | none => refusedBecause config tenant provider (.noSession outcome.refused) cookies
            | some _ =>
              finish .seeOther "" cookies (some (tenantConfig.returnTo completion.returnTo))
          -- A link issues nothing and touches no session cookie: whoever asked was signed in
          -- when they asked and still is (AUTH-6.7.1).
          | .linked _ =>
            finish .seeOther "" [cleared] (some (tenantConfig.returnTo completion.returnTo))
          | .linkRefused _ reason =>
            refusedBecause config tenant provider (.linkRefused reason) [cleared]

route_table Federated [
  start := "/t/:tenant:String/federated/:provider:String",
  callback := "/t/:tenant:String/federated/:provider:String/callback"
]

/-- The callback path is the one `callbackUri` builds, because the provider sends the browser to
the URI that was registered and nowhere else. That the two agree is worth a test rather than a
comment. -/
def routes [Clock IO] [RandomBytes IO] (config : Config) : List (Routing.Route Routing.Result) :=
  [ .get Federated.patterns.start (start config),
    .post Federated.patterns.start (linkStart config),
    .get Federated.patterns.callback (fun t p => complete config t p false),
    .post Federated.patterns.callback (fun t p => complete config t p true) ]

/-- Mount this wherever the application's own router is, as the sign-in routes are mounted. -/
def handler [Clock IO] [RandomBytes IO] (config : Config) : StatelessHandler :=
  Routing.toHandler (routes config) (fun _ => notFound config)

end Authentication.OidcHttp
