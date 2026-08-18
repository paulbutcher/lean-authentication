/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Authentication
import Codec.Base64Url
import Lean.Data.Json

/-!
SES bounce and complaint notifications (AUTH-12.1).

SES does not call a webhook; it publishes to SNS, and SNS posts a JSON envelope whose `Message`
is the SES payload as a string. Both layers are unwrapped here, because a client should not have
to know that its bounces arrive wrapped in someone else's transport.

Verifying that the delivery came from SNS is the receiving route's, as it is for Postmark: SNS
signs its posts with a certificate the route fetches and checks, and the route is also what
answers the subscription confirmation. Neither is possible from here, and a client that skips
them has published an endpoint by which anyone can suppress any address.

An unrecognised payload yields no events. SES sends deliveries, opens and rejections down the
same subscription, and an endpoint that fails on them is one SNS eventually stops calling.
-/

namespace Authentication.Ses

open Lean (Json)

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

end Authentication.Ses
