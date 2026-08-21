/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import AuthenticationSes
import AuthenticationPostmark
import AuthenticationSqlite

/-!
The SES transport (AUTH-10.9, AUTH-10.13), and the email flow through it.

No network (AUTH-16.5): the HTTP seam is filled by a fake that records what was asked of it. What
that leaves untested is libcurl and SES itself; what it covers is every decision this library makes
about them.

The signature is not checked against a golden value here. Whether the arithmetic is right is
`leanaws`'s question and its own suite answers it against AWS's published cases; what this suite
owns is the part that is this library's decision, which is what goes into the request being signed:
the credential scope, the set of headers signed, and that what was signed is also what is sent.
-/

namespace Tests.Ses
open Authentication Authentication.Service

private def address (raw : String) : EmailAddress := (EmailAddress.parse raw).toOption.getD default

def config : Ses.Config :=
  { region := "eu-west-1"
    credentials :=
      { accessKeyId := "AKIDEXAMPLE"
        secretAccessKey := "wJalrXUtnFEMI/K7MDENG+bPxRfiCYEXAMPLEKEY" }
    configurationSetName := some "auth-events" }

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
  | some bytes => (String.fromUTF8? bytes).getD ""
  | none => ""

private def stub (response : Except Leancurl.CurlError Leancurl.Response)
    (recorded : IO.Ref (Option Leancurl.Request)) : Ses.Http IO where
  send request := do
    recorded.set (some request)
    pure response

private def responding (status : UInt32) (body : String)
    (headers : Leancurl.Headers := []) : Leancurl.Response :=
  { status, headers, body := body.toUTF8 }

private def answering (status : UInt32) (body : String)
    (headers : Leancurl.Headers := []) : Except Leancurl.CurlError Leancurl.Response :=
  .ok (responding status body headers)

/-- Postmark stands beside SES in one check below, so it needs a seam of its own here. -/
private def postmarkConfig : Postmark.Config := { serverToken := "token-abc" }

private def postmarkStub (response : Except Leancurl.CurlError Leancurl.Response) :
    Postmark.Http IO where
  send _ := pure response

private def failure (errorName : String) (message : String) (status : UInt32) :
    Except SendError SentMessageId :=
  Ses.outcome
    { status
      headers := [("x-amzn-ErrorType", errorName ++ ":http://internal.amazon.com/coral/")]
      body := ("{\"message\":\"" ++ message ++ "\"}").toUTF8 }

private def errorOf : Except SendError SentMessageId → Option SendError
  | .error e => some e
  | .ok _ => none

private def sentIdOf : Except SendError SentMessageId → Option String
  | .ok id => some id.value
  | .error _ => none

/-- The instant the flow tests run at, rendered by the signer as `20231114T221320Z`. -/
private def now : Timestamp := ⟨1700000000⟩

private def signed : Leancurl.Request := Ses.request config now mail

private def allowedTagChar (c : Char) : Bool :=
  c.isAlphanum || c == '-' || c == '_'

def checks : List (String × Bool) :=
  let body := bodyText signed
  [ ("ses: the request goes to the region's endpoint",
      signed.url == "https://email.eu-west-1.amazonaws.com/v2/email/outbound-emails"),
    ("ses: the credential scope names the region and the service",
      (headerValue signed "Authorization").map
          (occurs "Credential=AKIDEXAMPLE/20231114/eu-west-1/ses/aws4_request") == some true),
    -- A header that is signed and not sent, or sent with another value, is a signature mismatch
    -- and nothing more informative, so the two lists have to agree.
    ("ses: what is signed is what is sent",
      (headerValue signed "Authorization").map
          (occurs "SignedHeaders=content-type;host;x-amz-date") == some true
        && headerValue signed "content-type" == some "application/json"
        && headerValue signed "x-amz-date" == some "20231114T221320Z"
        && (signed.headers.filter fun h => h.1.toLower == "content-type").length == 1),
    ("ses: the payload carries the sender, the recipient and both body parts",
      occurs "\"FromEmailAddress\"" body && occurs "\"person@example.com\"" body
        && occurs "\"Text\"" body && occurs "\"Html\"" body),
    ("ses: a subject containing a quote does not break the payload",
      (Json.parse body).toOption.isSome),
    ("ses: the configuration set is named, without which no event carries the tag back",
      occurs "\"ConfigurationSetName\":\"auth-events\"" body),
    -- SES accepts only letters, digits, hyphen and underscore in a tag value, and rejects the
    -- send otherwise. Substituting the offending characters would map two attempts onto one tag.
    ("ses: the idempotency key survives SES's tag alphabet intact",
      (Ses.tagValue "attempt:a1").all allowedTagChar
        && Codec.Base64Url.decodeString (Ses.tagValue "attempt:a1")
             == some "attempt:a1".toUTF8),
    ("ses: an accepted send yields the provider's message id",
      sentIdOf (Ses.outcome (responding 200 "{\"MessageId\":\"0100018b-abc\"}"))
        == some "0100018b-abc"),
    ("ses: a rejected recipient is a permanent failure",
      (errorOf (failure "MessageRejected" "Email address is not verified" 400)).map
        SendError.isPermanent == some true),
    ("ses: throttling is transient",
      errorOf (failure "TooManyRequestsException" "Maximum sending rate exceeded" 400)
        == some .rateLimited),
    -- An account in the sandbox, or a sending identity nobody has verified yet, is the operator's
    -- problem. It resolves without the person who asked for the link doing anything, so telling
    -- them their address was rejected would be false.
    ("ses: a suspended account is the operator's problem, not the recipient's",
      (errorOf (failure "AccountSuspendedException" "Your account is suspended" 400)).map
        SendError.isPermanent == some false),
    ("ses: a provider 5xx is transient",
      (errorOf (failure "InternalFailure" "oops" 500)).map SendError.isPermanent == some false),
    ("ses: a 200 carrying no message id is a failure rather than a silent success",
      (errorOf (Ses.outcome { status := 200, headers := [], body := "{}".toUTF8 })).isSome) ]

/-! ## The flow -/

initialize clockRef : IO.Ref Timestamp ← IO.mkRef ⟨1700000000⟩
initialize drawCounter : IO.Ref Nat ← IO.mkRef 0

instance : Clock IO where
  now := clockRef.get

instance : RandomBytes IO where
  draw count := do
    let index ← drawCounter.modifyGet fun n => (n, n + 1)
    pure (.ok ((Crypto.Sha256.hashUtf8 s!"ses-seed-{index}").extract 0 count))

def tenant : TenantId := ⟨"acme-ses"⟩

def tenantConfig : TenantConfig tenant :=
  { displayName := "Acme"
    baseUrl := ⟨"https://auth.example.com"⟩
    sendingIdentity :=
      { address := address "sign-in@auth.example.com", displayName := "Acme sign-in" }
    signupPolicy := .unrestricted }

/-- Two transports behind one port is the whole of AUTH-10.9's reasoning, so the flow is run
through both and the port is asked to produce the same kind of answer from each. -/
def flowChecks : IO (List (String × Bool)) := do
  let recorded ← IO.mkRef none
  let db ← Sqlite.openInMemory
  let ports : Ports IO :=
    { store := Sqlite.store db
      transport := Ses.transportWith (stub (answering 200 "{\"MessageId\":\"ses-1\"}") recorded)
        config
      responsePolicy := SignInResponsePolicy.silent IO
      limiter := RateLimiter.unlimited IO
      responseFloor := ResponseFloor.immediate IO
      humanCheck := HumanCheck.unchecked IO
      peppers := { current := { keyId := ⟨"pepper-1"⟩,
                                secret := Crypto.Sha256.hashUtf8 "test pepper" } } }
  let _ ← begin ports tenantConfig (address "person@example.com") { ip := some "198.51.100.7" }
  let request := (← recorded.get).getD { url := "" }
  let body := bodyText request
  let viaSes ← (Ses.transportWith
    (stub (answering 200 "{\"MessageId\":\"ses-1\"}") recorded) config).send mail
  let viaPostmark ← (Postmark.transportWith
    (postmarkStub (answering 200 "{\"ErrorCode\":0,\"MessageID\":\"pm-1\"}")) postmarkConfig).send mail
  pure
    [ ("ses flow: beginning a sign-in sends through the transport", (← recorded.get).isSome),
      ("ses flow: the message is addressed to the person who asked",
        occurs "\"person@example.com\"" body),
      ("ses flow: the subject is the tenant's template's",
        occurs "Sign in to Acme" body),
      ("ses flow: the magic link reaches the payload",
        occurs "https://auth.example.com/t/acme-ses" body),
      ("ses flow: the request is signed",
        (headerValue request "Authorization").map (occurs "/ses/aws4_request") == some true),
      ("ses flow: one OutboundEmail yields a message id from either transport",
        sentIdOf viaSes == some "ses-1" && sentIdOf viaPostmark == some "pm-1") ]

end Tests.Ses
