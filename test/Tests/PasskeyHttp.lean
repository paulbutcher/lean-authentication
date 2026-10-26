/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import AuthenticationPasskeyHttp
import AuthenticationSqlite
import RoutingStd
import Std.Http.Test.Helpers
import Tests.Fixtures.Authenticator

/-!
The passkey routes (§18.3).

What is route-specific is checked here and not in `Tests.PasskeyFlow`: which routes require a
session, that a refusal says the same thing whichever refusal it was, that the ceremony cookie is
set, and that the headers every response in this library carries are on these too.
-/

namespace Tests.PasskeyHttp
open Authentication Authentication.PasskeyHttp
open Authentication.Service Authentication.Passkey
open Std.Http.Internal.Test

initialize clockRef : IO.Ref Timestamp ← IO.mkRef ⟨1700000000⟩
initialize drawCounter : IO.Ref Nat ← IO.mkRef 0

instance : Clock IO where
  now := clockRef.get

instance : RandomBytes IO where
  draw count := do
    let index ← drawCounter.modifyGet fun n => (n, n + 1)
    pure (.ok ((Leancrypto.Sha256.hashUtf8 s!"passkey-http-seed-{index}").extract 0 count))

private def base : BaseUrl := ⟨"https://auth.example.test"⟩
private def tenant : TenantId := ⟨"acme"⟩

private def address (raw : String) : EmailAddress := (EmailAddress.parse raw).toOption.getD default

private def peppers : PepperRing :=
  { current :=
    { keyId := ⟨"pepper-1"⟩, secret := Leancrypto.Sha256.hashUtf8 "passkey http pepper" } }

private def liveConfig : TenantConfig tenant :=
  { displayName := "Acme"
    baseUrl := base
    sendingIdentity := { address := address "s@auth.example.test", displayName := "Acme" }
    signupPolicy := .unrestricted
    passkeyRelyingParty := some { id := "example.test", origins := [base.origin] } }

private def resolver (t : TenantId) : IO (Option (TenantConfig t)) :=
  if h : t = tenant then pure (some (h ▸ liveConfig)) else pure none

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
  let served : TestHandler := fun request => (handler (e := .std) config).onRequest request
  try
    check "passkey-http" raw served fun bytes =>
      captured.set ((String.fromUTF8? bytes).getD "")
  catch _ => pure ()
  captured.get

private def statusOf (response : String) : String :=
  ((response.splitOn "\x0d\n").head?.getD "").trimAscii.toString

private def headerOf (response name : String) : Option String :=
  ((response.splitOn "\x0d\n\x0d\n").head?.getD "").splitOn "\x0d\n" |>.findSome? fun line =>
    match line.splitOn ":" with
    | key :: rest =>
      if key.trimAscii.toString.toLower == name then
        some (String.intercalate ":" rest).trimAscii.toString
      else none
    | [] => none

private def bodyOf (response : String) : String :=
  ((response.splitOn "\x0d\n\x0d\n").drop 1).head?.getD ""

private def jsonHeaders : String :=
  "Content-Type: application/json\x0d\nConnection: close\x0d\n"

/-- A capture standing where the tenant goes, so what is compared is that the segment falls in
the same place on both sides rather than that a name equals a copy of itself. -/
private def anyTenant : TenantId := ⟨":tenant:String"⟩

/--
The completion routes sit under the route that begins their ceremony.

Each pair is one place as far as a client is concerned, and a table that drifted would leave a
page posting its result to a path that answers nothing. The assertion is textual because that is
all a pattern is before it is matched.
-/
theorem completionPathsNest :
    Routing.renderPattern Passkey.patterns.registerComplete =
        Routing.renderPattern Passkey.patterns.register ++ "/complete"
      ∧ Routing.renderPattern Passkey.patterns.signInComplete =
        Routing.renderPattern Passkey.patterns.signIn ++ "/complete"
      ∧ Routing.renderPattern Passkey.patterns.recoverComplete =
        Routing.renderPattern Passkey.patterns.recover ++ "/complete" := by decide

/--
Every passkey route answers under the tenant path the cookies are scoped to.

A route outside it would be served a ceremony cookie the browser never offers back, which is a
flow that works until the second request and then silently does not.
-/
theorem routesAreUnderTheTenantPath :
    Routing.renderPattern Passkey.patterns.register =
        BaseUrl.tenantPath anyTenant ++ "/passkey/register"
      ∧ Routing.renderPattern Passkey.patterns.signIn =
        BaseUrl.tenantPath anyTenant ++ "/passkey/signin"
      ∧ Routing.renderPattern Passkey.patterns.recover =
        BaseUrl.tenantPath anyTenant ++ "/passkey/recover" := by decide

def checks : IO (List (String × Bool)) := do
  let db ← Sqlite.openInMemory
  let ports := portsOn db
  let made ← issueFor ports liveConfig
    { origin := .magicLink ⟨"attempt-1"⟩
      address := address "holder@example.test"
      requester := {} }
  let session := ((made.setCookies.find? (·.name == "auth_session")).map (·.value)).getD ""
  let config : Config := { ports, verifier, tenant := resolver }

  let anonymousRegister ← send config (mkPost "/t/acme/passkey/register" "" jsonHeaders)
  let heldRegister ← send config
    (mkPost "/t/acme/passkey/register" ""
      (jsonHeaders ++ s!"Cookie: auth_session={session}\x0d\n"))
  let beganSignIn ← send config (mkPost "/t/acme/passkey/signin" "" jsonHeaders)
  -- A completion carrying no ceremony cookie, and one carrying nothing readable at all: two
  -- different refusals, which have to look the same.
  let noCookie ← send config
    (mkPost "/t/acme/passkey/signin/complete" "{\"id\":\"abc\"}" jsonHeaders)
  let notJson ← send config (mkPost "/t/acme/passkey/signin/complete" "not json" jsonHeaders)
  let unknownTenant ← send config (mkPost "/t/other/passkey/signin" "" jsonHeaders)

  let signInCookie := (headerOf beganSignIn "set-cookie").getD ""

  pure
    [ ("passkey http: a registration with no session starts nothing",
        statusOf anonymousRegister == "HTTP/1.1 400 Bad Request"
          && (headerOf anonymousRegister "set-cookie").isNone),
      ("passkey http: a registration with a session answers options and a ceremony cookie",
        statusOf heldRegister == "HTTP/1.1 200 OK"
          && ((headerOf heldRegister "set-cookie").getD "").startsWith "auth_passkey="
          && ((bodyOf heldRegister).splitOn "\"challenge\"").length == 2
          && ((bodyOf heldRegister).splitOn "\"excludeCredentials\"").length == 2),
      ("passkey http: the registration options name the relying party and require a resident key",
        ((bodyOf heldRegister).splitOn "example.test").length ≥ 2
          && ((bodyOf heldRegister).splitOn "\"residentKey\":\"required\"").length == 2),
      ("passkey http: an authentication begins with no session and names no credentials",
        statusOf beganSignIn == "HTTP/1.1 200 OK"
          && signInCookie.startsWith "auth_passkey="
          && ((bodyOf beganSignIn).splitOn "\"rpId\"").length == 2),
      ("passkey http: the ceremony cookie is confined to the tenant and not sent cross-site",
        (signInCookie.splitOn "Path=/t/acme").length == 2
          && (signInCookie.splitOn "SameSite=Strict").length == 2
          && (signInCookie.splitOn "HttpOnly").length == 2),
      ("passkey http: two different refusals answer with the same body (AUTH-14.2.3)",
        statusOf noCookie == statusOf notJson && bodyOf noCookie == bodyOf notJson
          && bodyOf noCookie != ""),
      ("passkey http: every response carries the headers the other routes carry",
        (headerOf beganSignIn "cache-control") == some "no-store"
          && (headerOf beganSignIn "x-frame-options") == some "DENY"
          && (headerOf noCookie "x-content-type-options") == some "nosniff"),
      ("passkey http: a tenant the resolver does not know is not found",
        statusOf unknownTenant == "HTTP/1.1 404 Not Found") ]

/-- The recovery routes, which are the registration routes with a grant where the session goes.
AUTH-22.21 holds because they are separate routes: the pair above still reads the account from
the session and nowhere else, and this pair reads it from the grant and nowhere else. -/
def recoveryChecks : IO (List (String × Bool)) := do
  let db ← Sqlite.openInMemory
  let ports := portsOn db
  let made ← issueFor ports liveConfig
    { origin := .magicLink ⟨"attempt-1"⟩
      address := address "holder@example.test"
      requester := {} }
  let account := (made.admitted.map (·.account)).getD ⟨""⟩
  let config : Config := { ports, verifier, tenant := resolver }

  let issued ← Service.createRecovery ports liveConfig account
  let (grant, token) := match issued with
    | .ok grantIssued => (grantIssued.grant.id, grantIssued.token)
    | .error _ => (⟨""⟩, ⟨""⟩)
  let body (g t : String) : String :=
    "{\"grant\":\"" ++ g ++ "\",\"token\":\"" ++ t ++ "\"}"

  let begun ← send config
    (mkPost "/t/acme/passkey/recover" (body grant.value token.encoded) jsonHeaders)
  let unknownGrant ← send config
    (mkPost "/t/acme/passkey/recover" (body "nope" "nope") jsonHeaders)
  let noBody ← send config (mkPost "/t/acme/passkey/recover" "" jsonHeaders)
  -- A grant in the body is not a session, so the ordinary registration route starts nothing.
  let atRegister ← send config
    (mkPost "/t/acme/passkey/register" (body grant.value token.encoded) jsonHeaders)

  pure
    [ ("passkey http: a recovery start needs no session, only the grant (AUTH-9.10.2)",
        statusOf begun == "HTTP/1.1 200 OK"
          && ((headerOf begun "set-cookie").getD "").startsWith "auth_passkey="
          && ((bodyOf begun).splitOn "\"challenge\"").length == 2),
      ("passkey http: the options name the relying party and still require a resident key",
        ((bodyOf begun).splitOn "example.test").length ≥ 2
          && ((bodyOf begun).splitOn "\"residentKey\":\"required\"").length == 2),
      ("passkey http: a grant nobody issued and no body at all answer alike (AUTH-14.2.3)",
        statusOf unknownGrant == statusOf noBody
          && bodyOf unknownGrant == bodyOf noBody
          && (headerOf unknownGrant "set-cookie").isNone),
      ("passkey http: a grant in the body does not stand in for a session at register",
        statusOf atRegister == "HTTP/1.1 400 Bad Request"
          && (headerOf atRegister "set-cookie").isNone) ]

/-- What a JSON body says under `name`, as a string. -/
private def member (response name : String) : String :=
  (((Lean.Json.parse (bodyOf response)).toOption.bind
    (·.getObjVal? name |>.toOption)).bind (·.getStr? |>.toOption)).getD ""

private def cookieValue (response : String) : String :=
  ((((headerOf response "set-cookie").getD "").splitOn ";").head?.getD "").drop
    "auth_passkey=".length |>.toString

/-- A whole sign-in through the routes, begun under `beganUnder` with `?returnTo=/after` and
completed under `completedUnder`, answering the completion's response. -/
private def signInVia (ports : Ports IO) (key : Libcrypto.Evp.PKey)
    (beganUnder completedUnder : TenantConfig tenant) : IO String := do
  let configOf (tenantConfig : TenantConfig tenant) : Config :=
    { ports, verifier, tenant := fun t =>
        if h : t = tenant then pure (some (h ▸ tenantConfig)) else pure none }
  let begun ← send (configOf beganUnder)
    (mkPost "/t/acme/passkey/signin?returnTo=/after" "" jsonHeaders)
  let clientData := Tests.Fixtures.Authenticator.clientDataFor base.origin
    assertionType (member begun "challenge")
  let authData := Tests.Fixtures.Authenticator.assertionAuthData "example.test" 0
  let signature ← Libcrypto.Sign.sign (.ecdsa .sha256) key
    (authData ++ Leancrypto.Sha256.hash clientData.toUTF8)
  let encode := Leancrypto.Codec.Base64Url.encodeString
  let payload := Lean.Json.mkObj
    [ ("id", .str Tests.Fixtures.Authenticator.handle.value),
      ("authenticatorData", .str (encode authData)),
      ("clientDataJSON", .str (encode clientData.toUTF8)),
      ("signature", .str (encode signature)) ]
  send (configOf completedUnder)
    (mkPost "/t/acme/passkey/signin/complete" payload.compress
      (jsonHeaders ++ s!"Cookie: auth_passkey={cookieValue begun}\x0d\n"))

/-- Where a completed sign-in says to land, which the page cannot work out for itself: it holds
neither the allowlist nor the target the ceremony stored (AUTH-22.23). -/
def returnToChecks : IO (List (String × Bool)) := do
  let db ← Sqlite.openInMemory
  let ports := portsOn db
  let made ← issueFor ports liveConfig
    { origin := .magicLink ⟨"attempt-1"⟩
      address := address "holder@example.test"
      requester := {} }
  let account := (made.admitted.map (·.account)).getD ⟨""⟩
  let (key, attestation) ← Tests.Fixtures.Authenticator.generate "example.test"
  let registering := (← Service.beginRegistration ports liveConfig account).toOption
  let _ ← Service.completeRegistration ports liveConfig account
    ((registering.map (·.cookie.value)).getD "") attestation
    (Tests.Fixtures.Authenticator.clientDataFor base.origin registrationType
      ((registering.map (·.challenge.encoded)).getD ""))
    "Laptop"

  let allowing := { liveConfig with returnToAllowlist := ["/after"], defaultReturnTo := "/home" }
  let allowed ← signInVia ports key allowing allowing
  let dropped ← signInVia ports key allowing { allowing with returnToAllowlist := [] }

  pure
    [ ("passkey http: a sign-in answers the target its ceremony carried, if allowed (AUTH-22.23)",
        member allowed "returnTo" == "/after"
          && ((bodyOf allowed).splitOn "\"signedIn\":true").length == 2),
      ("passkey http: a target the allowlist dropped mid-ceremony becomes the default (AUTH-22.23)",
        member dropped "returnTo" == "/home"
          && ((bodyOf dropped).splitOn "\"signedIn\":true").length == 2) ]

end Tests.PasskeyHttp
