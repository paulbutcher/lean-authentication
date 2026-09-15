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


/-! ## The routes over the wire -/

section Wire
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


private def address (raw : String) : EmailAddress := (EmailAddress.parse raw).toOption.getD default

/-- A provider whose discovery document will not read, so both legs of the flow refuse before
they reach it. -/
private def undiscoverablePorts : SignInPorts IO :=
  { oidcPorts with metadata := { discover := fun _ => pure (.error (.badDocument "issuer")) } }

/-- A provider that asserts an address and does not say it has verified it, which AUTH-6.7
refuses whatever else is true. -/
private def unverifiedPorts : SignInPorts IO :=
  { oidcPorts with
    identities :=
      { redeem := fun _ _ _ _ _ _ _ _ => pure (.ok
          { identity := ⟨provider.issuer, "subject-1"⟩
            address := some (address "person@example.test")
            addressVerified := false
            hostedDomain := none }) } }

/-- One request against these routes, and whatever the refusal port was told while it ran. -/
private def observing (ports : Ports IO) (oidc : SignInPorts IO) (raw : String) :
    IO (String × List String) := do
  let seen ← IO.mkRef ([] : List String)
  let response ← send
    { ports, oidc, tenant := resolver,
      observeRefusal := fun _ _ reason => seen.modify (· ++ [reason.name]) } raw
  pure (response, ← seen.get)

private def bodyOf (response : String) : String :=
  ((response.splitOn "\x0d\n\x0d\n").drop 1).head?.getD ""

private def callbackOf (state : String) : String :=
  mkGet s!"/t/acme/federated/google/callback?code=abc&state={state}"
    s!"Connection: close\x0d\nCookie: auth_federation={state}\x0d\n"

private def stateOf (response : String) : String :=
  ((headerValue response "location").bind (parameter · "state")).getD ""

/-- A link start, carrying the session cookie it was given or none at all. -/
private def linkPost (session : Option String) : String :=
  mkPost "/t/acme/federated/google" ""
    ("Content-Type: application/x-www-form-urlencoded\x0d\nConnection: close\x0d\n"
      ++ (match session with
          | some value => s!"Cookie: auth_session={value}\x0d\n"
          | none => ""))

/--
Each refusal the federated routes can answer with reaches the operator under its own name, while
the page stays the one page (AUTH-14.2.6, AUTH-14.2.4).

One request per refusal the routes decide for themselves, each driven through the handler, so
that what is established is the wiring and not the naming: a site left unwired reports nothing
here even though `Refusal.name` still answers. The pages are compared with each other rather than
with a literal, because what matters is that they do not differ.
-/
def refusalChecks : IO (List (String × Bool)) := do
  let db ← Sqlite.openInMemory
  let ports := portsOn db

  let (noCode, noCodeSeen) ← observing ports oidcPorts
    (mkGetClose "/t/acme/federated/google/callback")
  let (_, startSeen) ← observing ports undiscoverablePorts
    (mkGetClose "/t/acme/federated/google")
  let (_, discoverySeen) ← observing ports undiscoverablePorts
    (mkGetClose "/t/acme/federated/google/callback?code=abc")
  let (unpaired, unpairedSeen) ← observing ports oidcPorts
    (mkGetClose "/t/acme/federated/google/callback?code=abc&state=unheld")

  let (begun, begunSeen) ← observing ports unverifiedPorts
    (mkGetClose "/t/acme/federated/google")
  let (unverified, unverifiedSeen) ← observing ports unverifiedPorts
    (callbackOf (stateOf begun))

  -- A link whose identity another account already holds, which is the takeover AUTH-6.7.1 is
  -- there to refuse.
  let accountFor (attempt raw : String) : IO (Outcome tenant) :=
    issueFor ports liveConfig
      { origin := .magicLink ⟨attempt⟩, address := address raw, requester := {} }
  let holder ← accountFor "attempt-2" "holder@example.test"
  let other ← accountFor "attempt-3" "other@example.test"
  let _ ← linkIdentity ports ((other.admitted.map (·.account)).getD ⟨""⟩)
    ⟨provider.issuer, "subject-1"⟩
  let session := ((holder.setCookies.find? (·.name == "auth_session")).map (·.value)).getD ""
  let (linkBegun, _) ← observing ports oidcPorts (linkPost (some session))
  let (refusedLink, linkSeen) ← observing ports oidcPorts (callbackOf (stateOf linkBegun))

  -- The three ways a start refuses, which the callback never reaches.
  let (_, noCookieSeen) ← observing ports oidcPorts (linkPost none)
  let (_, strangeSeen) ← observing ports oidcPorts (linkPost (some "not-a-session"))
  revokeAllSessions (tenant := tenant) ports ((holder.admitted.map (·.account)).getD ⟨""⟩)
  let (_, revokedSeen) ← observing ports oidcPorts (linkPost (some session))
  let throttling : Ports IO := { ports with limiter := { admit := fun _ _ _ => pure false } }
  let (_, throttledSeen) ← observing throttling oidcPorts
    (mkGetClose "/t/acme/federated/google")

  pure
    [ ("oidc http: a callback carrying no code is a named refusal", noCodeSeen == ["no-code"])
    , ("oidc http: so is a provider whose discovery document will not read, on either leg",
        startSeen == ["bad-document"] && discoverySeen == ["bad-document"])
    , ("oidc http: so is a callback whose state the browser does not hold",
        unpairedSeen == ["nonce-mismatch"])
    , ("oidc http: so is an address the provider has not verified (AUTH-6.7)",
        unverifiedSeen == ["address-not-verified"])
    , ("oidc http: so is a link to an identity another account holds (AUTH-6.7.1)",
        linkSeen == ["already-linked"])
    , ("oidc http: a link start with no session cookie says that, and not that it was rejected",
        noCookieSeen == ["no-session-cookie"])
    , ("oidc http: a cookie matching no session and one matching a revoked one are held apart",
        strangeSeen == ["session-unknown"] && revokedSeen == ["session-revoked"])
    , ("oidc http: a throttled start is reported as throttled (AUTH-14.1.1)",
        throttledSeen == ["throttled"])
    , ("oidc http: a start that works reports nothing", begunSeen == [])
    , ("oidc http: and every one of them is the same page",
        [unpaired, unverified, refusedLink].all fun response =>
          statusOf response == statusOf noCode && bodyOf response == bodyOf noCode) ]

end Wire

end Tests.OidcHttp
