/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import AuthenticationPostmark
import AuthenticationSqlite

/-!
The Postmark transport (AUTH-10.6), and the email flow through it.

No network (AUTH-16.5): the HTTP seam is filled by a fake that records what was asked of it and
answers with payloads captured from the API (AUTH-16.4). What that leaves untested is libcurl
and Postmark itself; what it covers is every decision this library makes about them.
-/

namespace Tests.Postmark
open Authentication Authentication.Service

private def address (raw : String) : EmailAddress := (EmailAddress.parse raw).toOption.getD default

def config : Postmark.Config := { serverToken := "token-abc" }

private def mail : OutboundEmail :=
  { «from» := { address := address "sign-in@auth.example.com", displayName := "Acme sign-in" }
    to := address "person@example.com"
    subject := "Sign in to \"Acme\""
    textBody := "line one\nline two"
    htmlBody := some "<p>hello</p>"
    idempotencyKey := "attempt:a1" }

private def occurs (needle haystack : String) : Bool := (haystack.splitOn needle).length > 1

private def headerValue (request : Leancurl.Request) (name : String) : Option String :=
  (request.headers.find? fun h => h.1 == name).map (·.2)

private def bodyText (request : Leancurl.Request) : String :=
  match request.body with
  | some bytes => String.fromUTF8! bytes
  | none => ""

/-- Records the request and answers with whatever it was primed with. -/
private def stub (response : Except Leancurl.CurlError Leancurl.Response)
    (recorded : IO.Ref (Option Leancurl.Request)) : Postmark.Http IO where
  send request := do
    recorded.set (some request)
    pure response

private def ok (status : UInt32) (body : String) : Except Leancurl.CurlError Leancurl.Response :=
  .ok { status, headers := [], body := body.toUTF8 }

/-- Captured from the API rather than written from the documentation, which is the difference
between a golden payload and a guess (AUTH-16.4). A live send answers `"OK"` where the test
token answers `"Test job accepted"`; nothing here reads that field. -/
private def accepted : String :=
  "{\"ErrorCode\":0,\"Message\":\"Test job accepted\"," ++
  "\"MessageID\":\"24c0bc72-4982-481e-9cdd-168f84e68fee\"," ++
  "\"SubmittedAt\":\"2026-08-15T16:41:36.9172958Z\",\"To\":\"person@example.com\"}"

private def suppressed : String :=
  "{\"ErrorCode\":406,\"Message\":\"You tried to send to recipients that have been marked as " ++
  "inactive.\"}"

/-- Postmark answers its own failures with an HTTP 422 whatever they are, so rate limiting and a
missing sender signature arrive the same way and are told apart only by `ErrorCode`. -/
private def throttled : String :=
  "{\"ErrorCode\":429,\"Message\":\"You have exceeded the number of API requests allowed.\"}"

private def noSignature : String :=
  "{\"ErrorCode\":400,\"Message\":\"You are trying to send email from an address that does not " ++
  "have a sender signature.\"}"

private def sentIdOf : Except SendError SentMessageId → Option String
  | .ok id => some id.value
  | .error _ => none

private def errorOf : Except SendError SentMessageId → Option SendError
  | .ok _ => none
  | .error e => some e

def checks : IO (List (String × Bool)) := do
  let recorded ← IO.mkRef none
  let sent ← (Postmark.transportWith (stub (ok 200 accepted) recorded) config).send mail
  let request := (← recorded.get).getD { url := "" }
  let body := bodyText request

  pure
    [ ("postmark: the server token travels in the documented header",
        headerValue request "X-Postmark-Server-Token" == some "token-abc"),
      ("postmark: the request is a JSON POST to the send endpoint",
        request.method == .post && request.url == "https://api.postmarkapp.com/email"
          && headerValue request "Content-Type" == some "application/json"),
      ("postmark: a bounded timeout is set, so a slow provider cannot hang the response",
        request.timeoutMs == some 5000),
      ("postmark: the transactional stream is used, not a broadcast one",
        occurs "\"MessageStream\":\"outbound\"" body),
      ("postmark: the idempotency key travels as metadata",
        occurs "\"idempotency-key\":\"attempt:a1\"" body),
      ("postmark: the sender is rendered with its display name",
        occurs "\"From\":\"Acme sign-in <sign-in@auth.example.com>\"" body),
      ("postmark: both body parts are sent",
        occurs "\"TextBody\"" body && occurs "\"HtmlBody\"" body),
      ("postmark: a subject containing a quote does not break the payload",
        (Lean.Json.parse body).toOption.isSome
          && !occurs "\"Subject\":\"Sign in to \"Acme\"\"" body),
      ("postmark: an accepted send yields the provider's message id",
        sentIdOf sent == some "24c0bc72-4982-481e-9cdd-168f84e68fee"),
      ("postmark: an inactive recipient is a permanent failure",
        errorOf (Postmark.outcome 422 suppressed) == some .addressSuppressed
          && (SendError.addressSuppressed).isPermanent),
      ("postmark: a rate limit is read from the body, where Postmark puts it, not the status",
        errorOf (Postmark.outcome 422 throttled) == some .rateLimited
          && !(SendError.rateLimited).isPermanent),
      ("postmark: a bare 429 from something in front of Postmark is still a rate limit",
        errorOf (Postmark.outcome 429 "") == some .rateLimited),
      ("postmark: a missing sender signature is the operator's problem, not the recipient's",
        (errorOf (Postmark.outcome 422 noSignature)).map SendError.isPermanent == some false),
      ("postmark: a provider 5xx is transient",
        (errorOf (Postmark.outcome 500 "{\"Message\":\"oops\"}")).map SendError.isPermanent
          == some false),
      ("postmark: a 200 carrying a non-zero error code is still a failure",
        (errorOf (Postmark.outcome 200 suppressed)) == some .addressSuppressed),
      ("postmark: a timeout is reported as a timeout, not a generic failure",
        errorOf (← (Postmark.transportWith
          (stub (.error (Leancurl.CurlError.ofCode Leancurl.CurlError.operationTimedOut)) recorded)
          config).send mail) == some .timedOut) ]

/-! ## The flow -/

initialize clockRef : IO.Ref Timestamp ← IO.mkRef ⟨1700000000⟩
initialize drawCounter : IO.Ref Nat ← IO.mkRef 0

instance : Clock IO where
  now := clockRef.get

instance : RandomBytes IO where
  draw count := do
    let index ← drawCounter.modifyGet fun n => (n, n + 1)
    pure (.ok ((Crypto.Sha256.hashUtf8 s!"postmark-seed-{index}").extract 0 count))

def tenant : TenantId := ⟨"acme-postmark"⟩

def tenantConfig : TenantConfig tenant :=
  { displayName := "Acme"
    baseUrl := ⟨"https://auth.example.com"⟩
    sendingIdentity :=
      { address := address "sign-in@auth.example.com", displayName := "Acme sign-in" }
    signupPolicy := .unrestricted }

/-- Beginning a sign-in has to reach Postmark carrying the rendered template, which is the join
these tests exist to check: the flow, the template, and the transport in one path. -/
def flowChecks : IO (List (String × Bool)) := do
  let recorded ← IO.mkRef none
  let db ← Sqlite.openInMemory
  let ports : Ports IO :=
    { store := Sqlite.store db
      transport := Postmark.transportWith (stub (ok 200 accepted) recorded) config
      responsePolicy := SignInResponsePolicy.silent IO
      peppers := { current := { keyId := ⟨"pepper-1"⟩,
                                secret := Crypto.Sha256.hashUtf8 "test pepper" } } }
  let _ ← begin ports tenantConfig (address "person@example.com") { ip := some "198.51.100.7" }
  let request := (← recorded.get).getD { url := "" }
  let body := bodyText request
  let metadataValue :=
    (((Lean.Json.parse body).toOption.bind fun payload =>
      (payload.getObjVal? "Metadata").toOption.bind fun metadata =>
        (metadata.getObjVal? "idempotency-key").toOption.bind fun value =>
          value.getStr?.toOption)).getD ""
  pure
    [ ("postmark flow: beginning a sign-in sends through the transport",
        (← recorded.get).isSome),
      ("postmark flow: the message is addressed to the person who asked",
        occurs "\"To\":\"person@example.com\"" body),
      ("postmark flow: the subject is the tenant's template's",
        occurs "\"Subject\":\"Sign in to Acme\"" body),
      ("postmark flow: the magic link reaches the payload",
        occurs "https://auth.example.com/t/acme-postmark" body),
      ("postmark flow: the idempotency key names the attempt",
        occurs "\"idempotency-key\":\"attempt:" body),
      -- Postmark caps a metadata name at 20 characters and a value at 80, and exceeding either
      -- fails the send rather than truncating. The value carries a generated attempt id, so an
      -- identifier that grows would break sending in production and nowhere else.
      ("postmark flow: the metadata name and value stay inside Postmark's limits",
        "idempotency-key".length ≤ 20 && metadataValue.length ≤ 80
          && metadataValue.length > "attempt:".length) ]

end Tests.Postmark
