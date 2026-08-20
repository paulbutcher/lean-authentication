/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Authentication
public import Aws.Sigv4
public import Lean.Data.Json
public import Leancurl

/-!
The Amazon SES outbound transport (AUTH-10.9, AUTH-10.13).

Everything SES knows about is here. The core library names a port and never a provider, so it
compiles without this target and a client using a different provider never builds it.

The HTTP call goes through `Http` rather than `Leancurl.Curl.send` directly, so that the whole
adapter, the payload it builds and the responses it interprets, can be exercised without a
network (AUTH-16.5).
-/

public section

namespace Authentication.Ses

open Lean (Json)

/--
Sending must not block a response beyond a short bounded timeout, so the timeout is part of the
configuration rather than left to libcurl's default of none at all (AUTH-10.5).
-/
structure Config where
  region : String
  credentials : Aws.Sigv4.Credentials
  /-- Names the set of event destinations SES publishes deliveries and bounces to. Without one the
  tag carrying the idempotency key is accepted and never reported back, which is half of what
  AUTH-10.11 asks the key to do. -/
  configurationSetName : Option String := none
  timeoutMs : UInt32 := 5000

def Config.host (config : Config) : String := s!"email.{config.region}.amazonaws.com"

def resourcePath : String := "/v2/email/outbound-emails"

/-- The seam a fake stands in for. -/
structure Http (m : Type → Type) where
  send : Leancurl.Request → m (Except Leancurl.CurlError Leancurl.Response)

def curlHttp : Http IO where
  send := Leancurl.Curl.send

/-! ## The request -/

private def addressText (address : EmailAddress) : String := address.render

private def identityText (identity : SendingIdentity) : String :=
  s!"{identity.displayName} <{addressText identity.address}>"

private def contentJson (data : String) : Json :=
  Json.mkObj [("Data", .str data), ("Charset", .str "UTF-8")]

private def headerJson (header : String × String) : Json :=
  Json.mkObj [("Name", .str header.1), ("Value", .str header.2)]

/--
SES accepts only letters, digits, hyphen and underscore in a tag value, which is exactly the
base64url alphabet, so the key travels encoded rather than with its other characters substituted.
Substitution would map two different attempts onto one tag, which is precisely what the key exists
to prevent (AUTH-10.4, AUTH-10.11).
-/
def tagValue (key : String) : String := Codec.Base64Url.encodeString key.toUTF8

/-- SES has no idempotency header, so the key travels as a tag, which it echoes on the delivery
and bounce events published to the configuration set (AUTH-10.11). -/
def requestJson (config : Config) (mail : OutboundEmail) : Json :=
  let bodyContent :=
    Json.mkObj <|
      [("Text", contentJson mail.textBody)]
      ++ (match mail.htmlBody with
          | some html => [("Html", contentJson html)]
          | none => [])
  let simple :=
    Json.mkObj <|
      [("Subject", contentJson mail.subject), ("Body", bodyContent)]
      ++ (if mail.headers.isEmpty then []
          else [("Headers", Json.arr (mail.headers.map headerJson).toArray)])
  Json.mkObj <|
    [ ("FromEmailAddress", .str (identityText mail.«from»)),
      ("Destination", Json.mkObj [("ToAddresses", Json.arr #[.str (addressText mail.to)])]),
      ("Content", Json.mkObj [("Simple", simple)]),
      ("EmailTags", Json.arr #[Json.mkObj
        [("Name", .str "idempotency-key"), ("Value", .str (tagValue mail.idempotencyKey))]]) ]
    ++ (match mail.replyTo with
        | some address => [("ReplyToAddresses", Json.arr #[.str (addressText address)])]
        | none => [])
    ++ (match config.configurationSetName with
        | some name => [("ConfigurationSetName", .str name)]
        | none => [])

/-- Signing needs the time, which arrives as an argument so that this stays a pure function of the
request and a test can pin it (AUTH-3.3). Epoch seconds before 1970 are not a case that arises. -/
def request (config : Config) (now : Timestamp) (mail : OutboundEmail) : Leancurl.Request :=
  let body := (requestJson config mail).compress.toUTF8
  let signed :=
    Aws.Sigv4.sign config.credentials
      { region := config.region, service := "ses" }
      ⟨now.epochSeconds.toNat⟩
      { method := "POST"
        path := resourcePath
        host := config.host
        headers := [("Content-Type", "application/json")]
        body := body }
  { url := s!"https://{config.host}{resourcePath}"
    method := .post
    -- Every header comes from the signer, `Content-Type` included. Adding one here as well would
    -- send it twice, and a header signed but sent differently is a signature mismatch and nothing
    -- more informative.
    headers := signed.headers
    body := some body
    timeoutMs := some config.timeoutMs }

/-! ## The response -/

private def field (body : Json) (name : String) : Option Json := (body.getObjVal? name).toOption

private def stringField (body : Json) (name : String) : Option String :=
  (field body name).bind fun value => value.getStr?.toOption

/-- SES names its failures in a header rather than in the status, and appends a URL to the name in
some responses. -/
private def errorType (response : Leancurl.Response) (body : Json) : String :=
  let named :=
    (response.headers.find? fun h => h.1.toLower == "x-amzn-errortype").map (·.2)
  match named.orElse fun _ => stringField body "__type" with
  | none => ""
  | some raw => match raw.splitOn ":" with
    | [] => raw
    | first :: _ => first

/--
The two failures an operator has to fix are transient in the sense of AUTH-10.10: a suspended
account and an unverified sending identity both resolve without the person who asked for the link
doing anything, and telling them their address was rejected would be false. They therefore fall
through to `providerFailure`, which is not permanent.

A recipient on the account suppression list arrives as `MessageRejected` like any other rejection.
Telling the two apart would mean matching on the prose of the message, which fails silently the
day AWS rewords it, so this reports the rejection it can see. Either way the answer is permanent,
and §12's suppression list is the library's own rather than the provider's.
-/
private def errorOfType (errorName detail : String) (status : UInt32) : SendError :=
  match errorName with
  | "MessageRejected" => .addressRejected detail
  | "TooManyRequestsException" | "LimitExceededException" => .rateLimited
  | _ => if status == 429 then .rateLimited else .providerFailure detail

def outcome (response : Leancurl.Response) : Except SendError SentMessageId :=
  let text := (String.fromUTF8? response.body).getD ""
  let parsed := (Json.parse text).toOption.getD (Json.mkObj [])
  if response.status == 200 then
    match stringField parsed "MessageId" with
    | some id => .ok ⟨id⟩
    | none => .error (.providerFailure "response carried no MessageId")
  else
    let detail :=
      match (stringField parsed "message").orElse fun _ => stringField parsed "Message" with
      | some m => m
      | none => text
    .error (errorOfType (errorType response parsed) detail response.status)

private def errorOfCurl (error : Leancurl.CurlError) : SendError :=
  if error.code == Leancurl.CurlError.operationTimedOut then .timedOut
  else .providerFailure error.message

def transportWith {m : Type → Type} [Monad m] [Clock m] (http : Http m) (config : Config) :
    EmailTransport m where
  send mail := do
    let now ← Clock.now
    match ← http.send (request config now mail) with
    | .error e => pure (.error (errorOfCurl e))
    | .ok response => pure (outcome response)

def transport [Clock IO] (config : Config) : EmailTransport IO := transportWith curlHttp config

end Authentication.Ses
