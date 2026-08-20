/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import AuthenticationHttp
import AuthenticationPostmark
import AuthenticationSqlite
import Std.Http.Test.Helpers

/-!
The sign-in routes, driven over the wire (AUTH-13.2, AUTH-16.5).

Requests go in as HTTP text and responses come back as HTTP text, through the real parser and
the real serialiser, against SQLite in memory. Nothing here reaches a network.

What is checked is the protocol, not the markup: statuses, headers, cookies, and where a
redirect points. The pages are a client's to replace (`Pages`), so a test that pinned their
structure would fail on a restyle and prove nothing (AUTH-16.4). The one place this suite reads
the HTML is to pull the anti-forgery token out of a form, which is what a browser does.
-/

namespace Tests.Http
open Authentication Authentication.Service
open Std.Http.Internal.Test

initialize clockRef : IO.Ref Timestamp ← IO.mkRef ⟨1700000000⟩
initialize drawCounter : IO.Ref Nat ← IO.mkRef 0
initialize sentRef : IO.Ref (List OutboundEmail) ← IO.mkRef []

instance : Clock IO where
  now := clockRef.get

instance : RandomBytes IO where
  draw count := do
    let index ← drawCounter.modifyGet fun n => (n, n + 1)
    pure (.ok ((Crypto.Sha256.hashUtf8 s!"http-seed-{index}").extract 0 count))

def capturing : EmailTransport IO where
  send mail := do
    sentRef.modify (· ++ [mail])
    pure (.ok ⟨mail.idempotencyKey⟩)

private def address (raw : String) : EmailAddress := (EmailAddress.parse raw).toOption.getD default

def peppers : PepperRing :=
  { current := { keyId := ⟨"pepper-1"⟩, secret := Crypto.Sha256.hashUtf8 "test pepper" } }

def tenant : TenantId := ⟨"acme"⟩

def config : TenantConfig tenant :=
  { displayName := "Acme"
    baseUrl := ⟨"https://auth.example.com"⟩
    sendingIdentity :=
      { address := address "sign-in@auth.example.com", displayName := "Acme sign-in" }
    signupPolicy := .unrestricted
    returnToAllowlist := ["/dashboard"] }

private def resolver (t : TenantId) : IO (Option (TenantConfig t)) :=
  if h : t = tenant then pure (some (h ▸ config)) else pure none

/-! ## Talking to the handler -/

/-- Sends one raw request and returns the raw response. A failure inside the harness comes back
as an empty response, which fails whatever was being checked rather than the whole run. -/
private def send (handler : Authentication.Http.Config) (raw : String) : IO String := do
  let captured ← IO.mkRef ""
  let served : TestHandler := fun request => (Authentication.Http.handler handler).onRequest request
  try
    check "http" raw served fun bytes =>
      captured.set ((String.fromUTF8? bytes).getD "")
  catch _ => pure ()
  captured.get

private def statusOf (response : String) : String :=
  ((response.splitOn "\x0d\n").head?.getD "")

private def headerNames (response : String) : List String :=
  let head := (response.splitOn "\x0d\n\x0d\n").head?.getD ""
  ((head.splitOn "\x0d\n").drop 1).filterMap fun line =>
    match line.splitOn ":" with
    | [] => none
    | name :: _ => if name.isEmpty then none else some name.toLower

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

/-- The `name=value` of a `Set-Cookie`, which is what a browser sends back. -/
private def cookiePair (response : String) (name : String) : Option String :=
  (headerValues response "set-cookie").findSome? fun value =>
    match (value.splitOn ";").head? with
    | some pair => if pair.trimAscii.toString.startsWith (name ++ "=") then some pair else none
    | none => none

/-- Reads a hidden field out of a rendered form, standing in for the browser that would post it
back. The one piece of markup this suite depends on, and it depends on the attribute names HTML
fixes rather than on anything the pages chose. -/
private def fieldValue (html : String) (name : String) : Option String :=
  ((html.splitOn s!"name=\"{name}\"").drop 1).head?.bind fun tail =>
    ((tail.splitOn "value=\"").drop 1).head?.map fun rest =>
      String.ofList (rest.toList.takeWhile (· != '"'))

private def parameterFrom (body : String) (name : String) : Option String :=
  ((body.splitOn (name ++ "=")).drop 1).head?.map fun tail =>
    String.ofList (tail.toList.takeWhile fun c => c != '&' && c != '\n' && c != ' ')

/-! ## The checks -/

private def portsOn (db : SQLite) : Ports IO :=
  { store := Sqlite.store db
    transport := capturing
    responsePolicy := SignInResponsePolicy.silent IO
    limiter := RateLimiter.unlimited IO
    responseFloor := ResponseFloor.immediate IO
    humanCheck := HumanCheck.unchecked IO
    peppers }

def checks : IO (List (String × Bool)) := do
  clockRef.set ⟨1700000000⟩
  sentRef.set []
  let db ← Sqlite.openInMemory
  let http : Authentication.Http.Config := { ports := portsOn db, tenant := resolver }

  let form ← send http (mkGetClose "/t/acme/signin")
  let unknownTenant ← send http (mkGetClose "/t/other/signin")
  let unrouted ← send http (mkGetClose "/t/acme/nothing")

  -- Asking for a link.
  let begun ← send http
    (mkPost "/t/acme/signin" "email=person%40example.com&returnTo=%2Fdashboard"
      "Content-Type: application/x-www-form-urlencoded\x0d\nConnection: close\x0d\n")
  let attemptCookie := (cookiePair begun "auth_attempt").getD ""
  let token := (fieldValue (bodyOf begun) "token").getD ""

  -- The link, opened on a device holding no cookie.
  let mail := (← sentRef.get)[0]?
  let mailBody := (mail.map (·.textBody)).getD ""
  let attemptId := (parameterFrom mailBody "attempt").getD ""
  let magicToken := (parameterFrom mailBody "token").getD ""
  let opened ← send http
    (mkGetClose s!"/t/acme/signin/link?attempt={attemptId}&token={magicToken}")
  let shown := displayCode (revealedCode peppers ⟨magicToken⟩)

  -- The code, typed back into the browser that asked.
  let cookieHeader := s!"Cookie: {attemptCookie}\x0d\n"
  let postHeaders :=
    "Content-Type: application/x-www-form-urlencoded\x0d\nConnection: close\x0d\n" ++ cookieHeader
  let forged ← send http
    (mkPost "/t/acme/signin/code" s!"code={shown}&token=not-the-token&returnTo=%2Fdashboard"
      postHeaders)
  let signedIn ← send http
    (mkPost "/t/acme/signin/code" s!"code={shown}&token={token}&returnTo=%2Fdashboard"
      postHeaders)

  pure
    [ ("http: the sign-in page is served", statusOf form == "HTTP/1.1 200 OK"),
      ("http: an authentication page refuses to be framed (AUTH-14.1.5)",
        headerValues form "x-frame-options" == ["DENY"]),
      ("http: a tenant the client does not know is not there (AUTH-4.1.3)",
        statusOf unknownTenant == "HTTP/1.1 404 Not Found"),
      ("http: and neither is a path no route claims",
        statusOf unrouted == "HTTP/1.1 404 Not Found"),
      ("http: asking for a link sets the attempt cookie (AUTH-5.2.5)",
        (cookiePair begun "auth_attempt").isSome),
      ("http: the cookie is confined to the tenant's path and hidden from script (AUTH-9.2)",
        (headerValues begun "set-cookie").any fun v =>
          contains v "Path=/t/acme" && contains v "HttpOnly" && contains v "Secure"
            && contains v "SameSite=Lax"),
      ("http: a link opened without the cookie shows the code rather than signing in (AUTH-5.2.2)",
        statusOf opened == "HTTP/1.1 200 OK" && contains (bodyOf opened) shown
          && (cookiePair opened "auth_session").isNone),
      ("http: a form posted without the token bound to the cookie is refused (AUTH-14.1.4)",
        statusOf forged == "HTTP/1.1 403 Forbidden"
          && (cookiePair forged "auth_session").isNone),
      ("http: the right code in the right browser issues a session (AUTH-9.2)",
        statusOf signedIn == "HTTP/1.1 303 See Other"
          && (cookiePair signedIn "auth_session").isSome),
      ("http: and lands where the tenant allowed (AUTH-9.8)",
        headerValues signedIn "location" == ["/dashboard"]),
      ("http: the attempt cookie is cleared once it is spent",
        (headerValues signedIn "set-cookie").any fun v =>
          contains v "auth_attempt=" && contains v "Max-Age=0") ]

/-- AUTH-14.2.4: the mechanical shape of the answer must not vary with the outcome. The service
equalised the time; this is the half that is a property of the response.

The two requests differ in everything the library can see: one address is sent to, the other is
suppressed and does no work at all. Nothing about the answer may say which was which.
-/
def equalisationChecks : IO (List (String × Bool)) := do
  clockRef.set ⟨1700000000⟩
  sentRef.set []
  let db ← Sqlite.openInMemory
  let ports := portsOn db
  let http : Authentication.Http.Config := { ports, tenant := resolver }
  let _ ← ingestDelivery (tenant := tenant) ports
    { address := address "gone@example.com", failure := .hardBounce, detail := "550" }

  let post (email : String) : IO String :=
    send http
      (mkPost "/t/acme/signin" s!"email={email}"
        "Content-Type: application/x-www-form-urlencoded\x0d\nConnection: close\x0d\n")
  let sent ← post "person%40example.com"
  let suppressed ← post "gone%40example.com"
  let malformed ← post "not-an-address"
  let delivered := (← sentRef.get).length

  let sameShape (a b : String) : Bool :=
    statusOf a == statusOf b
      && headerNames a == headerNames b
      && (headerValues a "set-cookie").length == (headerValues b "set-cookie").length

  pure
    [ ("http: only the address that can be sent to is sent to", delivered == 1),
      ("http: a suppressed address answers in the same shape as one that was sent to",
        sameShape sent suppressed),
      ("http: so does an address that does not parse", sameShape sent malformed),
      ("http: every one of them sets exactly one cookie",
        (headerValues sent "set-cookie").length == 1
          && (headerValues suppressed "set-cookie").length == 1
          && (headerValues malformed "set-cookie").length == 1),
      ("http: and the decoy is the attempt cookie, not something shaped differently",
        (cookiePair suppressed "auth_attempt").isSome
          && (cookiePair suppressed "auth_attempt") != (cookiePair sent "auth_attempt")) ]

/-- The bot-mitigation hook on the send endpoint (AUTH-14.1.8). What the check does is the
client's; that it is asked, that a failure sends nothing, and that a failure is indistinguishable
from a send are not. -/
def humanCheckChecks : IO (List (String × Bool)) := do
  clockRef.set ⟨1700000000⟩
  sentRef.set []
  let db ← Sqlite.openInMemory
  let asked ← IO.mkRef 0
  let demanding : HumanCheck IO :=
    { verify := fun _ proof => do
        asked.modify (· + 1)
        pure (proof == some "solved") }
  let http : Authentication.Http.Config :=
    { ports := { portsOn db with humanCheck := demanding }
      tenant := resolver
      humanProofField := some "cf-turnstile-response" }

  let post (body : String) : IO String :=
    send http
      (mkPost "/t/acme/signin" body
        "Content-Type: application/x-www-form-urlencoded\x0d\nConnection: close\x0d\n")
  let unsolved ← post "email=person%40example.com"
  let sentAfterFailure := (← sentRef.get).length
  let solved ← post "email=person%40example.com&cf-turnstile-response=solved"
  let sentAfterSuccess := (← sentRef.get).length

  pure
    [ ("http: the send endpoint asks the bot-mitigation port (AUTH-14.1.8)",
        (← asked.get) == 2),
      ("http: a request that fails the challenge sends nothing",
        sentAfterFailure == 0 && sentAfterSuccess == 1),
      ("http: and is answered in the same shape as one that passed (AUTH-14.2.4)",
        statusOf unsolved == statusOf solved
          && headerNames unsolved == headerNames solved
          && (headerValues unsolved "set-cookie").length == 1) ]

/-- The provider callback route (AUTH-12.1.1). The endpoint's own verification is checked in
`Tests.Webhooks`; what is checked here is that the route reaches it, that a refusal reaches the
provider as a refusal, and that an accepted event actually lands in the store. -/
def webhookChecks : IO (List (String × Bool)) := do
  clockRef.set ⟨1700000000⟩
  sentRef.set []
  let db ← Sqlite.openInMemory
  let ports := portsOn db
  let credentials : Postmark.Credentials := { username := "hook", password := "s3cret" }
  let http : Authentication.Http.Config :=
    { ports, tenant := resolver, webhooks := [Postmark.endpoint credentials] }

  let bounce :=
    "{\"RecordType\":\"Bounce\",\"Type\":\"HardBounce\",\"Email\":\"gone@example.com\"," ++
    "\"Description\":\"550 5.1.1\"}"
  let post (path : String) (auth : Option String) : IO String :=
    send http
      (mkPost path bounce
        ("Content-Type: application/json\x0d\nConnection: close\x0d\n"
          ++ (match auth with
              | some value => s!"Authorization: {value}\x0d\n"
              | none => "")))
  let right := "Basic " ++ Codec.Base64.encodeString "hook:s3cret".toUTF8

  let unauthorised ← post "/t/acme/webhooks/postmark" none
  let afterRefusal ← suppressed (tenant := tenant) ports (address "gone@example.com")
  let delivered ← post "/t/acme/webhooks/postmark" (some right)
  let afterDelivery ← suppressed (tenant := tenant) ports (address "gone@example.com")
  let unconfigured ← post "/t/acme/webhooks/ses" (some right)
  let otherTenant ← post "/t/other/webhooks/postmark" (some right)

  pure
    [ ("http: a callback that cannot prove who sent it is refused (AUTH-12.1.1)",
        statusOf unauthorised == "HTTP/1.1 403 Forbidden"),
      ("http: and suppresses nothing", !afterRefusal),
      ("http: a verified callback is accepted and its event recorded (AUTH-12.1)",
        statusOf delivered == "HTTP/1.1 200 OK" && afterDelivery),
      ("http: a provider nobody configured has no endpoint",
        statusOf unconfigured == "HTTP/1.1 404 Not Found"),
      ("http: nor does a tenant the client does not know",
        statusOf otherTenant == "HTTP/1.1 404 Not Found") ]

/-- A redirect target the tenant did not allow is not followed (AUTH-9.8). The theorem in
`Tests.Session` says an unallowlisted target is never returned; this says the route asks. -/
def returnToChecks : IO (List (String × Bool)) := do
  clockRef.set ⟨1700000000⟩
  sentRef.set []
  let db ← Sqlite.openInMemory
  let http : Authentication.Http.Config := { ports := portsOn db, tenant := resolver }

  let begun ← send http
    (mkPost "/t/acme/signin" "email=person%40example.com"
      "Content-Type: application/x-www-form-urlencoded\x0d\nConnection: close\x0d\n")
  let attemptCookie := (cookiePair begun "auth_attempt").getD ""
  let token := (fieldValue (bodyOf begun) "token").getD ""
  let mailBody := (((← sentRef.get)[0]?).map (·.textBody)).getD ""
  let attemptId := (parameterFrom mailBody "attempt").getD ""
  let magicToken := (parameterFrom mailBody "token").getD ""
  let _ ← send http (mkGetClose s!"/t/acme/signin/link?attempt={attemptId}&token={magicToken}")
  let shown := displayCode (revealedCode peppers ⟨magicToken⟩)
  let signedIn ← send http
    (mkPost "/t/acme/signin/code"
      s!"code={shown}&token={token}&returnTo=https%3A%2F%2Fevil.test%2F"
      ("Content-Type: application/x-www-form-urlencoded\x0d\nConnection: close\x0d\n"
        ++ s!"Cookie: {attemptCookie}\x0d\n"))

  pure
    [ ("http: a redirect target nobody allowed becomes the tenant's default (AUTH-9.8)",
        statusOf signedIn == "HTTP/1.1 303 See Other"
          && headerValues signedIn "location" == ["/"]) ]

private def codedConfig : TenantConfig tenant := { config with emailedCodeEnabled := true }

private def codedResolver (t : TenantId) : IO (Option (TenantConfig t)) :=
  if h : t = tenant then pure (some (h ▸ codedConfig)) else pure none

private def emailedCodeIn (body : String) : Option String :=
  ((body.splitOn "Or type this code instead: ").drop 1).head?.map fun tail =>
    String.ofList (tail.toList.takeWhile Char.isDigit)

/-- The optional code in the mail body (AUTH-5.4). It is offered only where the tenant enabled
one, and it signs in without the link having been opened at all, which is the whole of its use.
-/
def emailedCodeChecks : IO (List (String × Bool)) := do
  clockRef.set ⟨1700000000⟩
  sentRef.set []
  let codedDb ← Sqlite.openInMemory
  let plainDb ← Sqlite.openInMemory
  let coded : Authentication.Http.Config := { ports := portsOn codedDb, tenant := codedResolver }
  let plain : Authentication.Http.Config := { ports := portsOn plainDb, tenant := resolver }
  let headers := "Content-Type: application/x-www-form-urlencoded\x0d\nConnection: close\x0d\n"

  let begun ← send coded
    (mkPost "/t/acme/signin" "email=person%40example.com&returnTo=%2Fdashboard" headers)
  let attemptCookie := (cookiePair begun "auth_attempt").getD ""
  let token := (fieldValue (bodyOf begun) "token").getD ""
  let typed := (emailedCodeIn ((((← sentRef.get)[0]?).map (·.textBody)).getD "")).getD ""
  let signedIn ← send coded
    (mkPost "/t/acme/signin/emailed-code" s!"code={typed}&token={token}&returnTo=%2Fdashboard"
      (headers ++ s!"Cookie: {attemptCookie}\x0d\n"))
  let withoutFlag ← send plain
    (mkPost "/t/acme/signin" "email=person%40example.com" headers)

  pure
    [ ("http: a tenant with typed codes enabled sends one (AUTH-5.4.1)", !typed.isEmpty),
      ("http: and the page it lands on offers somewhere to type it",
        contains (bodyOf begun) "/t/acme/signin/emailed-code"),
      ("http: a tenant without them is offered nothing",
        !contains (bodyOf withoutFlag) "/t/acme/signin/emailed-code"),
      ("http: the emailed code signs in without the link being opened (AUTH-5.4.2)",
        statusOf signedIn == "HTTP/1.1 303 See Other"
          && (cookiePair signedIn "auth_session").isSome) ]

end Tests.Http
