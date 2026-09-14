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

structure Config where
  ports : Service.Ports IO
  oidc : SignInPorts IO
  /-- The client's own lookup, as the sign-in routes take (AUTH-4.1.3). -/
  tenant : (t : TenantId) → IO (Option (TenantConfig t))
  /-- What a refusal renders as. The default says nothing about which of the refusals it was,
  which is the enumeration-resistant choice AUTH-14.2.3 makes elsewhere. -/
  refusedPage : String := "<!doctype html><title>Sign-in failed</title><p>That sign-in could not be completed.</p>"
  notFoundPage : String := "<!doctype html><title>Not found</title>"

/-- Where the provider sends the browser back. Built from the tenant's base URL, so it is the
same string a deployment registers with the provider and the same one the token request repeats
(AUTH-4.3.4). -/
def callbackUri {tenant : TenantId} (config : TenantConfig tenant) (provider : ProviderId) :
    String :=
  (config.baseUrl.url tenant ("/federated/" ++ provider.value ++ "/callback")).value

private def notFound (config : Config) : ContextAsync (Response Body.Any) :=
  finish .notFound config.notFoundPage []

private def refused (config : Config) : ContextAsync (Response Body.Any) :=
  finish .ok config.refusedPage []

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

/--
Sends the browser to the provider (AUTH-6.1).

`303` rather than `302`, so that a `POST` from a sign-in page becomes the `GET` the provider's
authorization endpoint expects rather than being replayed against it.
-/
private def start [Clock IO] [RandomBytes IO] (config : Config) (rawTenant rawProvider : String) :
    Routing.Result := fun request =>
  withProvider config rawTenant rawProvider fun _tenant tenantConfig provider => do
    let returnTo := (request.line.uri.query.get "returnTo")
    match ← (config.oidc.metadata.discover provider : IO _) with
    | .error _ => refused config
    | .ok discovery =>
      match ← (beginFederated config.ports.store config.ports.peppers tenantConfig provider
          discovery (callbackUri tenantConfig provider.id) returnTo
          ((request.line.uri.query.get "invitation").map (⟨·⟩)) : IO _) with
      | none => refused config
      | some begun =>
        let now ← (Clock.now : IO _)
        finish .seeOther "" [setCookie now begun.cookie] (some begun.authorizationUrl)

/--
The provider's answer (AUTH-6.2, AUTH-6.5, AUTH-6.7).

Everything a refusal could report is answered with the same page, for the reason AUTH-14.2.4
equalises the other route's: which of the refusals it was describes the person rather than the
tenant, and this route has no way to ask what the client wanted said.
-/
private def complete [Clock IO] [RandomBytes IO] (config : Config)
    (rawTenant rawProvider : String) (fromBody : Bool) : Routing.Result := fun request =>
  withProvider config rawTenant rawProvider fun tenant tenantConfig provider => do
    let query ← if fromBody then formBody request else pure request.line.uri.query
    let held := cookieNamed request "auth_federation"
    let cleared := clearCookie tenantConfig.baseUrl "auth_federation" (BaseUrl.tenantPath tenant)
    match query.get "code" with
    | none => finish .ok config.refusedPage [cleared]
    | some code =>
      match ← (config.oidc.metadata.discover provider : IO _) with
      | .error _ => finish .ok config.refusedPage [cleared]
      | .ok discovery =>
        match ← (completeFederated config.ports config.oidc tenantConfig provider discovery
            (callbackUri tenantConfig provider.id) (query.get "state") held code
            (requesterOf request) (query.get "user") : IO _) with
        | .error _ => finish .ok config.refusedPage [cleared]
        | .ok completion =>
          let now ← (Clock.now : IO _)
          let cookies := cleared :: completion.outcome.setCookies.map (setCookie now)
          match completion.outcome.session with
          | none => finish .ok config.refusedPage cookies
          | some _ =>
            finish .seeOther "" cookies (some (tenantConfig.returnTo completion.returnTo))

route_table Federated [
  start := "/t/:tenant:String/federated/:provider:String",
  callback := "/t/:tenant:String/federated/:provider:String/callback"
]

/-- The callback path is the one `callbackUri` builds, because the provider sends the browser to
the URI that was registered and nowhere else. That the two agree is worth a test rather than a
comment. -/
def routes [Clock IO] [RandomBytes IO] (config : Config) : List (Routing.Route Routing.Result) :=
  [ .get Federated.patterns.start (start config),
    .get Federated.patterns.callback (fun t p => complete config t p false),
    .post Federated.patterns.callback (fun t p => complete config t p true) ]

/-- Mount this wherever the application's own router is, as the sign-in routes are mounted. -/
def handler [Clock IO] [RandomBytes IO] (config : Config) : StatelessHandler :=
  Routing.toHandler (routes config) (fun _ => notFound config)

end Authentication.OidcHttp
