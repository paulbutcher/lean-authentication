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
    returnToAllowlist := ["/dashboard", "/back"] }

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

/-! ## The cookie the target rides in -/

section CookieFormat
open Authentication.Http Codec.Base64Url

private theorem sextet_range : ∀ n ∈ List.range 64, encodeSextet n ≠ ':' := by decide

private theorem encodeSextet_ne_colon (n : Nat) : encodeSextet n ≠ ':' := by
  rcases Nat.lt_or_ge n 64 with h | h
  · exact sextet_range n (List.mem_range.mpr h)
  · have hlen : alphabet.length ≤ n := by
      show (64 : Nat) ≤ n
      omega
    rw [show encodeSextet n = '=' by simp [encodeSextet, List.getD_eq_getElem?_getD,
      List.getElem?_eq_none hlen]]
    decide

/-- The separator must not turn up inside the field the target is encoded into, or the split
that recovers the attempt and the nonce would find four fields and hand back nothing. -/
private theorem colon_not_mem_encode (l : List UInt8) : ':' ∉ encode l := by
  induction l using encode.induct with
  | case1 => simp [encode]
  | case2 a => simp [encode, encodeSextet_ne_colon, Ne.symm]
  | case3 a b => simp [encode, encodeSextet_ne_colon, Ne.symm]
  | case4 a b c rest ih => simp [encode, encodeSextet_ne_colon, Ne.symm, ih]

private theorem colon_not_mem_encodeString (bytes : ByteArray) :
    ':' ∉ (encodeString bytes).toList := by
  simp [encodeString, String.toList_ofList, colon_not_mem_encode]

/--
Everything the attempt cookie carries survives being written and read back: the attempt and the
nonce whatever was asked for, and the target itself whenever it was short enough to be carried
at all. A cookie that lost the first two would not be a broken redirect but a broken sign-in,
which is why this is a theorem rather than a handful of examples.

The `:` hypotheses hold of what the core mints, both of which are base64url. `codec` is
`leancrypto`'s base64url round trip: it is proved in that library's own suite but not exported
from it, and copying the proof here would be this suite testing a dependency. Everything else
the claim rests on is proved above.
-/
theorem parse_withReturnTo {tenant : TenantId} (attempt : AttemptId tenant)
    (nonce : CredentialValue) (target : Option String)
    (ha : ':' ∉ attempt.value.toList) (hn : ':' ∉ nonce.encoded.toList)
    (codec : ∀ s : String, decodeString (encodeString s.toUTF8) = some s.toUTF8) :
    AttemptCookie.parse (tenant := tenant)
        (AttemptCookie.withReturnTo (Attempt.cookieValue attempt nonce) target)
      = some ⟨attempt, nonce, target.filter (·.utf8ByteSize ≤ AttemptCookie.returnToLimit)⟩ := by
  have dropped : AttemptCookie.parse (tenant := tenant)
      (Attempt.cookieValue attempt nonce) = some ⟨attempt, nonce, none⟩ := by
    simp [AttemptCookie.parse, Attempt.cookieValue, String.toList_append,
      List.splitOn_append_cons_self_of_not_mem ha, List.splitOn_eq_singleton hn]
  match target with
  | none => simpa [AttemptCookie.withReturnTo] using dropped
  | some t =>
    by_cases h : t.utf8ByteSize > AttemptCookie.returnToLimit
    · simp only [AttemptCookie.withReturnTo, AttemptCookie.encodeReturnTo, Option.bind_some,
        if_pos h]
      simpa [Option.filter, Nat.not_le.mpr h] using dropped
    · have hc : decodeString (encodeString t.toByteArray) = some t.toByteArray := codec t
      have hu : String.fromUTF8? t.toByteArray = some t := by
        simp [String.fromUTF8?, String.fromUTF8, t.isValidUTF8]
      simp only [AttemptCookie.withReturnTo, AttemptCookie.encodeReturnTo, Option.bind_some,
        if_neg h]
      simp [AttemptCookie.parse, Attempt.cookieValue, String.toList_append,
        List.splitOn_append_cons_self_of_not_mem ha,
        List.splitOn_append_cons_self_of_not_mem hn,
        List.splitOn_eq_singleton (colon_not_mem_encodeString t.toByteArray),
        AttemptCookie.decodeReturnTo, hc, hu, Option.filter, Nat.not_lt.mp h]

end CookieFormat


/-! ## The target, on its way into the header -/

section LocationHeader
open Authentication.Http Std.Http.Internal.Char

/-- The encoded reading of a redirect target: bytes that stand for themselves, and well-formed
triplets. This is what a caller who encoded a target once leaves behind after the form parser
decoded it once, and it is what `ReturnTo.base` splits and what a `Location` has to hold. -/
private def encodedReference : List UInt8 → Bool
  | [] => true
  | p :: d₁ :: d₂ :: rest =>
    if p = '%'.toUInt8 then isHexDigitByte d₁ && isHexDigitByte d₂ && encodedReference rest
    else locationChar p && encodedReference (d₁ :: d₂ :: rest)
  | c :: rest => locationChar c && encodedReference rest
  termination_by bytes => bytes.length

/-- A target that is already a URI reference reaches the browser as it was asked for: nothing in
it is escaped, so nothing in it is escaped twice. A counterexample is not a redirect that merely
looks wrong; it is one that arrives at a different place, because the application at the other
end decodes what it is given once and finds `%3A` where the caller wrote `:`. -/
theorem escapeLocation_of_encodedReference (bytes : List UInt8) (h : encodedReference bytes) :
    escapeLocation bytes = bytes.map Char.ofUInt8 := by
  fun_induction escapeLocation bytes <;> simp_all [encodedReference, escapeByte] <;>
    first | decide | (split at h <;> simp_all)

end LocationHeader

/-- The same-device path (AUTH-5.2.1): the person opens the mailed link rather than typing the
code back. The link carries the attempt and its token and nothing else, so the target rides in
the attempt cookie, and a confirm `POST` naming no target of its own must still land on it. -/
def sameDeviceReturnToChecks : IO (List (String × Bool)) := do
  clockRef.set ⟨1700000000⟩
  let db ← Sqlite.openInMemory
  let http : Authentication.Http.Config := { ports := portsOn db, tenant := resolver }
  let headers := "Content-Type: application/x-www-form-urlencoded\x0d\nConnection: close\x0d\n"

  -- Ask for a link, open it on the device that asked, and confirm without naming a target.
  let confirmed (asked : String) : IO String := do
    sentRef.set []
    let begun ← send http
      (mkPost "/t/acme/signin" s!"email=person%40example.com{asked}" headers)
    let attemptCookie := (cookiePair begun "auth_attempt").getD ""
    let mailBody := (((← sentRef.get)[0]?).map (·.textBody)).getD ""
    let attemptId := (parameterFrom mailBody "attempt").getD ""
    let magicToken := (parameterFrom mailBody "token").getD ""
    let opened ← send http
      (mkGet s!"/t/acme/signin/link?attempt={attemptId}&token={magicToken}"
        s!"Connection: close\x0d\nCookie: {attemptCookie}\x0d\n")
    let token := (fieldValue (bodyOf opened) "token").getD ""
    send http
      (mkPost "/t/acme/signin/confirm" s!"token={token}"
        (headers ++ s!"Cookie: {attemptCookie}\x0d\n"))

  let allowed ← confirmed "&returnTo=%2Fdashboard"
  let refused ← confirmed "&returnTo=https%3A%2F%2Fevil.test%2F"
  -- The allowlist matches everything before the query, so a padded query is an allowed target
  -- of any length, which is what tells the cap apart from the allowlist.
  let within := String.ofList (List.replicate 1000 'a')
  let beyond := String.ofList (List.replicate 1100 'a')
  let long ← confirmed s!"&returnTo=%2Fdashboard%3Ffrom%3D{within}"
  let tooLong ← confirmed s!"&returnTo=%2Fdashboard%3Ffrom%3D{beyond}"
  -- Not ASCII, so a header value cannot hold it as it stands. What comes back must be the
  -- escaped form of what was asked for, with the characters that carry the structure of a URI
  -- left alone: escaping those would move the query or the fragment rather than preserve it.
  let multibyte ← confirmed "&returnTo=%2Fdashboard%3Ffrom%3Dcaf%C3%A9%23top"
  -- A caller with a target of its own to preserve encodes it once for the form field, and the
  -- form parser decodes it once, so what arrives here is a URI reference with its triplets still
  -- in it. Escaping those again would land the browser somewhere else: the application at the
  -- far end decodes its query once, and would find the text `https%3A%2F%2Fx.example%2Fcb` where
  -- a URL was meant.
  let carried ← confirmed "&returnTo=%2Fback%3Fu%3Dhttps%253A%252F%252Fx.example%252Fcb"
  -- A target that would end the header line early and start a header of its own.
  let injected ← confirmed "&returnTo=%2Fdashboard%3Fx%3D%0D%0AX-Injected%3A%20yes"
  let unasked ← confirmed ""

  pure
    [ ("http: a target asked for at the start survives the mailed link (AUTH-9.8)",
        statusOf allowed == "HTTP/1.1 303 See Other"
          && headerValues allowed "location" == ["/dashboard"]),
      ("http: and one the tenant did not allow becomes the default however it arrived",
        statusOf refused == "HTTP/1.1 303 See Other"
          && headerValues refused "location" == ["/"]),
      ("http: a target within the cap arrives whole, query and all",
        headerValues long "location" == [s!"/dashboard?from={within}"]),
      ("http: a target that no header value could hold is escaped, not dropped",
        statusOf multibyte == "HTTP/1.1 303 See Other"
          && headerValues multibyte "location" == ["/dashboard?from=caf%C3%A9#top"]),
      ("http: a target whose query is itself encoded is not encoded a second time (AUTH-9.8)",
        statusOf carried == "HTTP/1.1 303 See Other"
          && headerValues carried "location" == ["/back?u=https%3A%2F%2Fx.example%2Fcb"]),
      ("http: a target carrying CR or LF cannot start a header of its own",
        statusOf injected == "HTTP/1.1 303 See Other"
          && headerValues injected "location" == ["/dashboard?x=%0D%0AX-Injected:%20yes"]
          && !(headerNames injected).contains "x-injected"),
      ("http: one past the cap is dropped rather than shortened, and costs the sign-in nothing",
        statusOf tooLong == "HTTP/1.1 303 See Other"
          && (cookiePair tooLong "auth_session").isSome
          && headerValues tooLong "location" == ["/"]),
      ("http: a cookie of the two fields written before targets rode in one still signs in",
        statusOf unasked == "HTTP/1.1 303 See Other"
          && (cookiePair unasked "auth_session").isSome) ]

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

/-! ## Reading parameters -/

private def queryFrom (raw : String) : Std.Http.URI.Query :=
  Middleware.ContentType.FormUrlEncoded.parse raw

private def refusedAs (expected : OAuth.OAuthError) {α : Type} : Except OAuth.OAuthError α → Bool
  | .error code => code == expected
  | .ok _ => false

private def yielded (expected : String) : Except OAuth.OAuthError String → Bool
  | .ok value => value == expected
  | .error _ => false

/-- Both of these would be theorems, but what they run through is the query parser of a
dependency, whose body does not reach this module: nothing here reduces at elaboration.

The first is the one that matters. A parameter sent twice has to arrive as two pairs, because
that is what lets `Params.single?` refuse it (OAuth 2.1 §4.1.1); a reader that collapsed the
query into a lookup would accept it, in exactly the case where somebody is trying something.
The second is why the decoding happens here rather than downstream: a lookup comparing
percent-encoded bytes compares a form that is not canonical. -/
def paramChecks : List (String × Bool) :=
  [ ("http: a parameter sent twice reaches the reader twice",
      refusedAs .invalidRequest
        ((OAuth.Params.ofQuery
          (queryFrom "resource=https%3A%2F%2Fa.test&resource=https%3A%2F%2Fb.test")).single?
            "resource"))
  , ("http: names and values are decoded before anything matches them",
      yielded "a b"
        ((OAuth.Params.ofQuery (queryFrom "code%5Fverifier=a%20b")).required "code_verifier")) ]

end Tests.Http
