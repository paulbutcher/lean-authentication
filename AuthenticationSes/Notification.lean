/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Authentication
public import AuthenticationSes.Transport
public import Codec.Base64
public import Codec.Base64Url
public import Crypto.Rsa
public import Der
import Json

/-!
SES bounce and complaint notifications (AUTH-12.1, AUTH-12.1.1).

SES does not call a webhook; it publishes to SNS, and SNS posts a JSON envelope whose `Message`
is the SES payload as a string. Both layers are unwrapped here, because a client should not have
to know that its bounces arrive wrapped in someone else's transport.

Establishing that a post came from SNS is three separate things, and skipping any one of them
leaves an endpoint by which somebody else decides which addresses stop receiving mail:

1. The signature must verify against the certificate the message names, and that certificate must
   be fetched from a host this library recognises rather than from whatever URL the payload asked
   for. `signingHostAllowed` is that check and it happens before the fetch.
2. The topic must be one the client expects. This is the one that looks optional and is not: the
   signature proves SNS sent the message, not that *your* topic did, and anyone with an AWS
   account can subscribe your endpoint to a topic of their own and post whatever they like
   through it.
3. The subscription handshake must be answered, or nothing arrives at all.

An unrecognised payload yields no events. SES sends deliveries, opens and rejections down the
same subscription, and an endpoint that fails on them is one SNS eventually stops calling.
-/

public section

namespace Authentication.Ses

private def field (payload : Json) (name : String) : Option Json :=
  (payload.getObjVal? name).toOption

private def stringField (payload : Json) (name : String) : Option String :=
  (field payload name).bind fun value => value.getStr?.toOption

private def arrayField (payload : Json) (name : String) : Array Json :=
  ((field payload name).bind fun value => value.getArr?.toOption).getD #[]

/-- The tag carrying the idempotency key is base64url of the key, because SES accepts only the
base64url alphabet in a tag value (AUTH-10.4). SES reports tags as an object of arrays. -/
private def reference (mail : Json) : Option String := do
  let tags ← field mail "tags"
  let values ← (tags.getObjVal? "idempotency-key").toOption
  let encoded ← (values.getArr?.toOption).bind fun entries =>
    entries[0]?.bind fun entry => entry.getStr?.toOption
  let decoded ← Codec.Base64Url.decodeString encoded
  String.fromUTF8? decoded

/-- `Permanent` is the only bounce SES will not retry. `Transient` and `Undetermined` are
counted and nothing more. -/
private def bounceFailure (bounceType : String) : DeliveryFailure :=
  if bounceType == "Permanent" then .hardBounce else .softBounce

private def eventsFrom (address : String) (failure : DeliveryFailure) (detail : String)
    (reference : Option String) : List DeliveryEvent :=
  match EmailAddress.parse address with
  | .error _ => []
  | .ok address => [{ address, failure, detail, reference }]

private def bounceEvents (payload : Json) (reference : Option String) : List DeliveryEvent :=
  match field payload "bounce" with
  | none => []
  | some bounce =>
    let failure := bounceFailure ((stringField bounce "bounceType").getD "")
    let subType := (stringField bounce "bounceSubType").getD ""
    (arrayField bounce "bouncedRecipients").toList.flatMap fun recipient =>
      match stringField recipient "emailAddress" with
      | none => []
      | some address =>
        let diagnostic := (stringField recipient "diagnosticCode").getD subType
        eventsFrom address failure diagnostic reference

private def complaintEvents (payload : Json) (reference : Option String) : List DeliveryEvent :=
  match field payload "complaint" with
  | none => []
  | some complaint =>
    let feedback := (stringField complaint "complaintFeedbackType").getD ""
    (arrayField complaint "complainedRecipients").toList.flatMap fun recipient =>
      match stringField recipient "emailAddress" with
      | none => []
      | some address => eventsFrom address .spamComplaint feedback reference

/-- The SES payload itself, once the SNS envelope is off. Configuration sets name the field
`eventType` and the older notification subscriptions name it `notificationType`; both are read,
because which one a deployment produces depends on how its topic was set up. -/
def eventsOfNotification (body : String) : List DeliveryEvent :=
  match Json.parse body with
  | .error _ => []
  | .ok payload =>
    let kind :=
      ((stringField payload "eventType").orElse fun _ =>
        stringField payload "notificationType").getD ""
    let reference := (field payload "mail").bind reference
    if kind == "Bounce" then bounceEvents payload reference
    else if kind == "Complaint" then complaintEvents payload reference
    else []

/-- What arrives at the endpoint: an SNS envelope carrying the SES payload as a string. A body
that is not one is read as the payload itself, so a client posting SES events by some other route
is not obliged to wrap them. -/
def deliveryEvents (body : String) : List DeliveryEvent :=
  match Json.parse body with
  | .error _ => []
  | .ok envelope =>
    match stringField envelope "Message" with
    | some message => eventsOfNotification message
    | none => eventsOfNotification body

/-! ## Establishing that SNS sent it -/

/--
The bytes SNS signed: each present field as its name, a newline, its value, and a newline, in the
order the field list gives. Which fields depends on the message type, and a field that is absent
contributes nothing rather than an empty value.
-/
def signedFields : String → List String
  | "SubscriptionConfirmation" | "UnsubscribeConfirmation" =>
    ["Message", "MessageId", "SubscribeURL", "Timestamp", "Token", "TopicArn", "Type"]
  | _ => ["Message", "MessageId", "Subject", "Timestamp", "TopicArn", "Type"]

def stringToSign (envelope : Json) : String :=
  String.join
    ((signedFields ((stringField envelope "Type").getD "")).filterMap fun name =>
      (stringField envelope name).map fun value => name ++ "\n" ++ value ++ "\n")

/--
`https://sns.<region>.amazonaws.com/...`, and nothing else without the client saying so. The host
is compared after the userinfo trap is closed: `https://sns.eu-west-1.amazonaws.com@evil.test/x`
has `evil.test` for its host and would pass a check written with `startsWith`.
-/
def hostOf (url : String) : Option String :=
  if !url.startsWith "https://" then none
  else
    let rest := String.ofList ((url.toList.drop 8).takeWhile (· != '/'))
    if rest.isEmpty || rest.toList.contains '@' || rest.toList.contains ':' then none
    else some rest

def signingHostAllowed (extra : List String) (host : String) : Bool :=
  extra.contains host ||
    (host.startsWith "sns." && host.endsWith ".amazonaws.com" &&
      let region := String.ofList
        ((host.toList.drop 4).take (host.length - 4 - ".amazonaws.com".length))
      !region.isEmpty && !region.toList.contains '.')

/-- Everything an endpoint needs that this library cannot decide or perform. -/
structure Subscription (m : Type → Type) where
  /-- The topics whose messages are accepted. Not optional, and not defaulted: see the module
  comment. An empty list accepts nothing, which is the right way round for a mistake. -/
  topics : List String
  /-- Fetches the signing certificate, as PEM, from a URL already checked against
  `signingHostAllowed`. -/
  certificate : String → m (Option String)
  /-- Visits the URL a `SubscriptionConfirmation` carried, which is what makes SNS start
  delivering. -/
  confirm : String → m Bool
  /-- Additional hosts a certificate may come from, for a partition beyond the standard one. -/
  extraSigningHosts : List String := []
  name : String := "ses"

private def fetched {m : Type → Type} [Monad m] (http : Http m) (url : String) (timeoutMs : UInt32) :
    m (Option String) := do
  match ← http.send { url, method := .get, timeoutMs := some timeoutMs } with
  | .error _ => pure none
  | .ok response =>
    if response.status == 200 then pure (String.fromUTF8? response.body) else pure none

/--
The default, over the same seam the transport uses so that both can be exercised without a
network (AUTH-16.5).

Every certificate is fetched afresh. SNS rotates the signing certificate rarely and names it in
the message, so a cache would help a busy endpoint, and a client that wants one wraps
`certificate` rather than finding one here that it cannot see the eviction policy of.
-/
def curlSubscriptionWith {m : Type → Type} [Monad m] (http : Http m) (topics : List String)
    (timeoutMs : UInt32 := 5000) : Subscription m where
  topics
  certificate url := fetched http url timeoutMs
  confirm url := do pure ((← fetched http url timeoutMs).isSome)

def curlSubscription (topics : List String) : Subscription IO :=
  curlSubscriptionWith curlHttp topics

/-- Why a post was refused. Not returned to the sender, which is told only that it was refused,
but worth having distinct for whoever has to work out why nothing is arriving. -/
inductive Refusal where
  | malformed
  | unsupportedSignatureVersion (version : String)
  | untrustedCertificateUrl (url : String)
  | certificateUnavailable
  | signatureInvalid
  | unexpectedTopic (topic : String)
  deriving Repr, DecidableEq, Inhabited

/--
Signature version 2 only, which is RSA over SHA-256. Version 1 is RSA over SHA-1 and is refused
rather than supported: it is a per-topic setting the client controls, so the cost of refusing is
a configuration change, and the alternative is carrying a broken hash to accommodate a default.
-/
def verify {m : Type → Type} [Monad m] (subscription : Subscription m) (envelope : Json) :
    m (Except Refusal Unit) := do
  let field name := stringField envelope name
  match field "SignatureVersion", field "SigningCertURL", field "Signature" with
  | some version, some url, some signature =>
    if version != "2" then return .error (.unsupportedSignatureVersion version)
    match hostOf url with
    | none => return .error (.untrustedCertificateUrl url)
    | some host =>
      if !signingHostAllowed subscription.extraSigningHosts host then
        return .error (.untrustedCertificateUrl url)
      match ← subscription.certificate url with
      | none => return .error .certificateUnavailable
      | some pem =>
        match Der.publicKeyOfPem pem, Codec.Base64.decodeString signature with
        | some key, some signatureBytes =>
          if Crypto.Rsa.verifyPkcs1v15Sha256 key (stringToSign envelope).toUTF8 signatureBytes then
            -- Only now is the topic worth reading: an unverified one is whatever the sender
            -- typed.
            let topic := (field "TopicArn").getD ""
            if subscription.topics.contains topic then pure (.ok ())
            else pure (.error (.unexpectedTopic topic))
          else pure (.error .signatureInvalid)
        | _, _ => pure (.error .certificateUnavailable)
  | _, _, _ => pure (.error .malformed)

/-- The route-facing endpoint (AUTH-12.1.1). Verification is not a separate call a route could
omit: nothing is parsed, confirmed or ingested until it has passed. -/
def endpoint {m : Type → Type} [Monad m] (subscription : Subscription m) : WebhookEndpoint m where
  name := subscription.name
  accept _tenant _header body :=
    match Json.parse body with
    | .error _ => pure .rejected
    | .ok envelope => do
      match ← verify subscription envelope with
      | .error _ => pure .rejected
      | .ok () =>
        match (stringField envelope "Type").getD "" with
        | "SubscriptionConfirmation" =>
          match stringField envelope "SubscribeURL" with
          | none => pure .rejected
          | some url => do
            let _ ← subscription.confirm url
            pure .accepted
        | "Notification" =>
          match (stringField envelope "Message").map eventsOfNotification with
          | some (event :: rest) => pure (.ingest (event :: rest))
          | _ => pure .accepted
        | _ => pure .accepted

end Authentication.Ses
