/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import AuthenticationOidcHttp
import AuthenticationSqlite
import Std.Http.Test.Helpers

/-!
The federated routes (§6).

The path the provider is told to send the browser back to, and the path the routes answer on, are
built independently. A disagreement between them is the failure nothing observes until a real
provider redirects: everything works except the half of the flow that comes back.
-/

namespace Tests.OidcHttp
open Authentication Authentication.OidcHttp

private def base : BaseUrl := ⟨"https://auth.example.test"⟩

/-- A route capture standing where a tenant identifier goes, so what is compared is that the
tenant segment falls in the same place on both sides. A real tenant name would compare a path
against a copy of itself and pass whatever the table said. -/
private def anyTenant : TenantId := ⟨":tenant:String"⟩

private def anyProvider : ProviderId := ⟨":provider:String"⟩

private def configFor (tenant : TenantId) : TenantConfig tenant :=
  { displayName := "Acme"
    baseUrl := base
    sendingIdentity :=
      { address := (EmailAddress.parse "s@auth.example.test").toOption.getD default
        displayName := "Acme" }
    signupPolicy := .unrestricted }

/--
The URI the provider is given is the URI the callback route answers on.

`Routing.renderPattern` prints the declared route as the path it matches, and `callbackUri` is
what `beginFederated` puts in the authorization request and what the token request repeats. Both
sides carry captures rather than names, so what is established is that the tenant and the provider
segments fall in the same places, which is the part a table could get wrong while every path
built from one configuration still agreed with itself.

The left-hand side drops the origin, because a pattern matches a path and `callbackUri` returns an
absolute URL; `base` is a constant here and the origin is `BaseUrl.url`'s to prepend.
-/
theorem callbackPathAgrees :
    base.origin ++ Routing.renderPattern Federated.patterns.callback =
      callbackUri (configFor anyTenant) anyProvider := by decide

/-- The start route is the callback's path without its last segment, which is what makes the pair
readable as one place rather than two. -/
theorem startPathAgrees :
    Routing.renderPattern Federated.patterns.callback =
      Routing.renderPattern Federated.patterns.start ++ "/callback" := by decide


/-! ## Starting a link over the wire -/

section LinkRoute
open Authentication.Service Authentication.Oidc
open Std.Http.Internal.Test

initialize clockRef : IO.Ref Timestamp ← IO.mkRef ⟨1700000000⟩
initialize drawCounter : IO.Ref Nat ← IO.mkRef 0

instance : Clock IO where
  now := clockRef.get

instance : RandomBytes IO where
  draw count := do
    let index ← drawCounter.modifyGet fun n => (n, n + 1)
    pure (.ok ((Leancrypto.Sha256.hashUtf8 s!"oidc-http-seed-{index}").extract 0 count))

private def peppers : PepperRing :=
  { current := { keyId := ⟨"pepper-1"⟩, secret := Leancrypto.Sha256.hashUtf8 "oidc http pepper" } }

private def tenant : TenantId := ⟨"acme"⟩

private def provider : ProviderConfig :=
  { id := ⟨"google"⟩
    issuer := "https://accounts.google.test"
    clientId := "client-1"
    credentials := .clientSecret (.external "vault://acme/google") }

private def liveConfig : TenantConfig tenant :=
  { displayName := "Acme"
    baseUrl := base
    sendingIdentity :=
      { address := (EmailAddress.parse "s@auth.example.test").toOption.getD default
        displayName := "Acme" }
    signupPolicy := .unrestricted
    providers := [provider] }

private def resolver (t : TenantId) : IO (Option (TenantConfig t)) :=
  if h : t = tenant then pure (some (h ▸ liveConfig)) else pure none

private def discovery : Discovery :=
  { issuer := provider.issuer
    authorizationEndpoint := "https://accounts.google.test/authorize"
    tokenEndpoint := "https://oauth2.google.test/token"
    jwksUri := "https://www.google.test/jwks" }

private def oidcPorts : SignInPorts IO :=
  { metadata := { discover := fun _ => pure (.ok discovery) }
    identities :=
      { redeem := fun _ _ _ _ _ _ _ _ => pure (.ok
          { identity := ⟨provider.issuer, "subject-1"⟩
            address := none
            addressVerified := false
            hostedDomain := none }) } }

private def portsOn (db : SQLite) : Ports IO :=
  { store := Sqlite.store db
    transport := EmailTransport.capturing (fun _ => pure ())
    responsePolicy := SignInResponsePolicy.silent IO
    limiter := RateLimiter.unlimited IO
    responseFloor := ResponseFloor.immediate IO
    humanCheck := HumanCheck.unchecked IO
    peppers }

private def send (config : Config) (raw : String) : IO String := do
  let captured ← IO.mkRef ""
  let served : TestHandler := fun request => (handler config).onRequest request
  try
    check "oidc-http" raw served fun bytes =>
      captured.set ((String.fromUTF8? bytes).getD "")
  catch _ => pure ()
  captured.get

private def statusOf (response : String) : String :=
  ((response.splitOn "\x0d\n").head?.getD "").trimAscii.toString

private def headerValue (response name : String) : Option String :=
  ((response.splitOn "\x0d\n\x0d\n").head?.getD "").splitOn "\x0d\n" |>.findSome? fun line =>
    match line.splitOn ":" with
    | key :: rest =>
      if key.trimAscii.toString.toLower == name then
        some (String.intercalate ":" rest).trimAscii.toString
      else none
    | [] => none

private def parameter (url name : String) : Option String :=
  ((url.splitOn (name ++ "=")).drop 1)[0]?.map fun tail =>
    String.ofList (tail.toList.takeWhile (· != '&'))

/--
The account a link is for comes from the session cookie, and a request without one starts nothing
(AUTH-6.7.1).

A cross-site `POST` carries no `SameSite=Lax` cookie, so this refusal is also what stops a link
being provoked from somebody else's page: the request arrives looking exactly like this one.
-/
def linkRouteChecks : IO (List (String × Bool)) := do
  let db ← Sqlite.openInMemory
  let ports := portsOn db
  let made ← issueFor ports liveConfig
    { origin := .magicLink ⟨"attempt-1"⟩
      address := (EmailAddress.parse "holder@example.test").toOption.getD default
      requester := { ip := none, userAgent := none, approximateLocation := none } }
  let account := (made.admitted.map (·.account)).getD ⟨""⟩
  let session := ((made.setCookies.find? (·.name == "auth_session")).map (·.value)).getD ""
  let config : Config := { ports, oidc := oidcPorts, tenant := resolver }
  let formHeaders :=
    "Content-Type: application/x-www-form-urlencoded\x0d\nConnection: close\x0d\n"

  let anonymous ← send config (mkPost "/t/acme/federated/google" "" formHeaders)
  let held ← send config
    (mkPost "/t/acme/federated/google" ""
      (formHeaders ++ s!"Cookie: auth_session={session}\x0d\n"))
  let forged ← send config
    (mkPost "/t/acme/federated/google" s!"account={account.value}" formHeaders)
  let signIn ← send config (mkGetClose "/t/acme/federated/google")

  let recordFor (response : String) : IO (Option (FederationState tenant)) := do
    match (headerValue response "location").bind (parameter · "state") with
    | none => pure none
    | some state =>
      ports.store.federationStateByDigest tenant ⟨1700000000⟩ (peppers.current.digest ⟨state⟩)
  let linkRecord ← recordFor held
  let signInRecord ← recordFor signIn

  pure
    [ ("oidc http: a link start with no session starts nothing (AUTH-6.7.1)",
        statusOf anonymous == "HTTP/1.1 200 OK" && (headerValue anonymous "location").isNone)
    , ("oidc http: naming an account in the body does not stand in for holding one",
        statusOf forged == "HTTP/1.1 200 OK" && (headerValue forged "location").isNone)
    , ("oidc http: a link start with a session goes to the provider",
        statusOf held == "HTTP/1.1 303 See Other"
          && ((headerValue held "location").getD "").startsWith discovery.authorizationEndpoint)
    , ("oidc http: and the account rides on the state record, not on the request",
        (linkRecord.bind (·.account)) == some account)
    , ("oidc http: a plain sign-in still starts one, bound to no account",
        statusOf signIn == "HTTP/1.1 303 See Other"
          && signInRecord.isSome && (signInRecord.bind (·.account)).isNone) ]

end LinkRoute

end Tests.OidcHttp
