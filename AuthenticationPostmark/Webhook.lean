/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Authentication
import Codec.Base64
import Crypto.Compare
import Lean.Data.Json

/-!
Postmark's bounce and spam-complaint webhooks (AUTH-12.1, AUTH-12.1.1).

Postmark authenticates its webhooks by presenting HTTP basic credentials the client configured
alongside the URL, so establishing that a payload came from Postmark is a comparison against
those credentials and nothing more. `endpoint` does it; `deliveryEvents` is the parser it uses,
public because a client receiving these some other way still needs to read one.

An unrecognised payload yields no events rather than an error. A webhook endpoint that fails on
an event type it was not expecting is one the provider eventually stops calling, and Postmark
sends record types this library has no use for down the same URL.
-/

public section

namespace Authentication.Postmark

open Lean (Json)

private def stringField (payload : Json) (name : String) : Option String :=
  ((payload.getObjVal? name).toOption).bind fun value => value.getStr?.toOption

/--
The types Postmark suppresses on, which are the types this library treats as permanent. The
others are transient by Postmark's own reckoning, and a mailbox that was full this morning is
not an address nobody may write to again.

`Unsubscribe` and `ManuallyDeactivated` are permanent here even though neither is a failure of
the address: both are somebody saying to stop, and continuing is worse than useless.
-/
private def failureOfType : String → DeliveryFailure
  | "HardBounce" | "BadEmailAddress" | "Blocked" | "ManuallyDeactivated" | "Unsubscribe" =>
    .hardBounce
  | "SpamNotification" => .spamComplaint
  | _ => .softBounce

/-- The idempotency key travels as metadata, which Postmark echoes back, so the key that stops a
double send is what names the attempt when the bounce arrives (AUTH-10.4). -/
private def reference (payload : Json) : Option String :=
  ((payload.getObjVal? "Metadata").toOption).bind fun metadata =>
    stringField metadata "idempotency-key"

private def detailOf (payload : Json) : String :=
  match stringField payload "Description", stringField payload "Details" with
  | some description, some details =>
    if details.isEmpty then description else description ++ " " ++ details
  | some description, none => description
  | none, some details => details
  | none, none => ""

/--
One payload as this library's own vocabulary. It is a list because the SES adapter's is, and a
client wiring two providers should not have to remember which one can report two addresses at
once.
-/
def deliveryEvents (body : String) : List DeliveryEvent :=
  match Json.parse body with
  | .error _ => []
  | .ok payload =>
    match stringField payload "Email", stringField payload "RecordType" with
    | some raw, some record =>
      match EmailAddress.parse raw with
      | .error _ => []
      | .ok address =>
        let failure :=
          if record == "SpamComplaint" then DeliveryFailure.spamComplaint
          else if record == "Bounce" then failureOfType ((stringField payload "Type").getD "")
          else DeliveryFailure.softBounce
        if record == "Bounce" || record == "SpamComplaint" then
          [{ address, failure, detail := detailOf payload, reference := reference payload }]
        else []
    | _, _ => []

/-! ## The endpoint -/

/-- What Postmark was configured to present. Supplied by configuration and never defaulted
(AUTH-14.1.6): a default would be a published password. -/
structure Credentials where
  username : String
  password : String

/-- Compared whole rather than field by field, and with `Crypto.bytesEqual` rather than `==`: the
latter stops at the first differing byte, which reports how long a correct prefix a guess had
(AUTH-5.3.4). This one is a password, so unlike the rest of this library's comparisons the
property is doing real work. -/
def authorised (credentials : Credentials) (header : Option String) : Bool :=
  let expected :=
    "Basic " ++ Codec.Base64.encodeString (credentials.username ++ ":" ++ credentials.password).toUTF8
  match header with
  | none => false
  | some offered => Crypto.bytesEqual offered.toUTF8 expected.toUTF8

/-- The route-facing endpoint (AUTH-12.1.1). Nothing reaches the parser until the credentials
match, which is why this is one call and not two. -/
def endpoint {m : Type → Type} [Pure m] (credentials : Credentials)
    (name : String := "postmark") : WebhookEndpoint m where
  name
  accept _tenant header body :=
    if !authorised credentials (header "authorization") then pure .rejected
    else
      match deliveryEvents body with
      | [] => pure .accepted
      | events => pure (.ingest events)

end Authentication.Postmark
