/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Authentication
import Lean.Data.Json

/-!
Postmark's bounce and spam-complaint webhooks (AUTH-12.1).

Reading a payload is all that happens here. Whether it really came from Postmark is the
receiving route's question, and the route is where the credential to answer it lives: Postmark
authenticates its webhooks with HTTP basic auth on a URL the client chose, and this library
never sees either. A client that skips the check has published an endpoint by which anyone can
suppress any address.

An unrecognised payload yields no events rather than an error. A webhook endpoint that fails on
an event type it was not expecting is one the provider eventually stops calling, and Postmark
sends record types this library has no use for down the same URL.
-/

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

end Authentication.Postmark
