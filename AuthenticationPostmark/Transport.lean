/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Authentication
public import Json
public import Leancurl

/-!
The Postmark outbound transport (AUTH-10.6).

Everything Postmark knows about is here. The core library names a port and never a provider, so
it compiles without this target and a client that uses a different provider never builds it.

The HTTP call goes through `Http` rather than `Leancurl.Curl.send` directly, so that the whole
adapter, the payload it builds and the responses it interprets, can be exercised without a
network (AUTH-16.5).
-/

public section

namespace Authentication.Postmark

/--
Sending must not block a response beyond a short bounded timeout, so the timeout is part of the
configuration rather than left to libcurl's default of none at all (AUTH-10.5).
-/
structure Config where
  serverToken : String
  /-- The transactional stream. A broadcast stream would be the wrong one: these are not
  marketing messages and must not be subject to bulk suppression. -/
  messageStream : String := "outbound"
  endpoint : String := "https://api.postmarkapp.com/email"
  timeoutMs : UInt32 := 5000

/-- The seam a fake stands in for. -/
structure Http (m : Type → Type) where
  send : Leancurl.Request → m (Except Leancurl.CurlError Leancurl.Response)

def curlHttp : Http IO where
  send := Leancurl.Curl.send

/-! ## The request -/

private def addressText (address : EmailAddress) : String := address.render

private def identityText (identity : SendingIdentity) : String :=
  s!"{identity.displayName} <{addressText identity.address}>"

private def headerJson (header : String × String) : Json :=
  Json.mkObj [("Name", .str header.1), ("Value", .str header.2)]

/--
Postmark has no idempotency header, so the key travels as metadata, which it echoes back on the
delivery and bounce webhooks. That makes the same key that prevents a double send the key that
identifies the attempt when the bounce arrives (AUTH-10.4).
-/
def requestJson (config : Config) (mail : OutboundEmail) : Json :=
  Json.mkObj <|
    [ ("From", .str (identityText mail.«from»)),
      ("To", .str (addressText mail.to)),
      ("Subject", .str mail.subject),
      ("TextBody", .str mail.textBody),
      ("MessageStream", .str config.messageStream),
      ("Metadata", Json.mkObj [("idempotency-key", .str mail.idempotencyKey)]) ]
    ++ (match mail.htmlBody with | some html => [("HtmlBody", Json.str html)] | none => [])
    ++ (match mail.replyTo with
        | some address => [("ReplyTo", Json.str (addressText address))]
        | none => [])
    ++ (if mail.headers.isEmpty then []
        else [("Headers", Json.arr (mail.headers.map headerJson).toArray)])

def request (config : Config) (mail : OutboundEmail) : Leancurl.Request :=
  { url := config.endpoint
    method := .post
    headers :=
      [ ("X-Postmark-Server-Token", config.serverToken),
        ("Content-Type", "application/json"),
        ("Accept", "application/json") ]
    body := some (requestJson config mail).compress.toUTF8
    timeoutMs := some config.timeoutMs }

/-! ## The response -/

private def field (body : Json) (name : String) : Option Json := (body.getObjVal? name).toOption

private def stringField (body : Json) (name : String) : Option String :=
  (field body name).bind fun value => value.getStr?.toOption

private def errorCode (body : Json) : Int :=
  ((field body "ErrorCode").bind fun value => value.getInt?.toOption).getD 0

private def message (body : Json) : String := (stringField body "Message").getD ""

/--
Postmark's own error codes, which are not HTTP statuses. Only the two that say something about
the address are permanent (AUTH-10.3). Everything else is retried, including the ones an
operator has to fix: a missing sender signature (400) and an account out of credits (405) both
start working again without the person who asked for the link doing anything, and telling them
their address was rejected would be false.
-/
private def errorOfCode (code : Int) (detail : String) : SendError :=
  match code with
  | 406 => .addressSuppressed
  | 300 => .addressRejected detail
  | 429 => .rateLimited
  | _ => .providerFailure detail

/--
Interprets a response. The code in the body decides, not the status: Postmark answers its own
failures with an HTTP 422 and distinguishes them in `ErrorCode`, rate limiting included, and it
reports some rejections with an HTTP success. The status is consulted only when the body says
nothing, which is where a proxy's 429 or a gateway's 502 arrives.
-/
def outcome (status : UInt32) (body : String) : Except SendError SentMessageId :=
  let parsed := (Json.parse body).toOption.getD (Json.mkObj [])
  let code := errorCode parsed
  let detail :=
    let text := message parsed
    if text.isEmpty then body else text
  if status == 200 && code == 0 then
    match stringField parsed "MessageID" with
    | some id => .ok ⟨id⟩
    | none => .error (.providerFailure "response carried no MessageID")
  else if code != 0 then
    .error (errorOfCode code detail)
  else if status == 429 then
    .error .rateLimited
  else
    .error (.providerFailure detail)

private def errorOfCurl (error : Leancurl.CurlError) : SendError :=
  if error.code == Leancurl.CurlError.operationTimedOut then .timedOut
  else .providerFailure error.message

def transportWith {m : Type → Type} [Monad m] (http : Http m) (config : Config) :
    EmailTransport m where
  send mail := do
    match ← http.send (request config mail) with
    | .error e => pure (.error (errorOfCurl e))
    | .ok response => pure (outcome response.status (String.fromUTF8! response.body))

def transport (config : Config) : EmailTransport IO := transportWith curlHttp config

end Authentication.Postmark
