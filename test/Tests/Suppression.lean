/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import AuthenticationPostmark
import AuthenticationSes
import AuthenticationSqlite

/-!
Bounces and suppression (§12).

Two providers report the same events in shapes that have nothing in common, so both parsers are
run against payloads in the shape the provider documents. What they must agree on is which
failures are permanent: a suppression that a transient failure could cause locks people out of
their own accounts because a mail server was busy.

The rest is driven through the service, because "refuses to send" is not visible in the store:
what has to be checked is that the transport was never asked.
-/

namespace Tests.Suppression
open Authentication Authentication.Service

/-! ## The invariant -/

/-- Once suppressed, only the client lifts it (AUTH-12.4). Everything the providers report can
add a suppression and nothing they report takes one away, which is what makes a bounce storm
followed by one soft bounce safe. -/
theorem afterFailure_suppressed {tenant : TenantId} (record : DeliveryRecord tenant)
    (failure : DeliveryFailure) (now : Timestamp) (detail : String) :
    (record.afterFailure failure now detail).suppressed
      = (failure.suppression.isSome || record.suppressed) := by
  simp only [DeliveryRecord.afterFailure, DeliveryRecord.suppressed]
  cases failure <;> simp [DeliveryFailure.suppression, Option.orElse]

/-! ## The provider payloads -/

private def postmarkBounce : String :=
  "{\"RecordType\":\"Bounce\",\"Type\":\"HardBounce\",\"TypeCode\":1," ++
  "\"Email\":\"Gone@Example.COM\",\"Description\":\"The server was unable to deliver\"," ++
  "\"Details\":\"550 5.1.1 unknown user\",\"BouncedAt\":\"2026-08-18T16:33:54Z\"," ++
  "\"Metadata\":{\"idempotency-key\":\"attempt:a-1\"}}"

private def postmarkTransient : String :=
  "{\"RecordType\":\"Bounce\",\"Type\":\"Transient\",\"TypeCode\":2," ++
  "\"Email\":\"busy@example.com\",\"Description\":\"Mailbox full\",\"Details\":\"\"}"

private def postmarkComplaint : String :=
  "{\"RecordType\":\"SpamComplaint\",\"Type\":\"SpamComplaint\",\"TypeCode\":100001," ++
  "\"Email\":\"cross@example.com\",\"Description\":\"Recipient marked as spam\"}"

private def postmarkDelivery : String :=
  "{\"RecordType\":\"Delivery\",\"Recipient\":\"person@example.com\"," ++
  "\"DeliveredAt\":\"2026-08-18T16:33:54Z\"}"

private def sesTag (key : String) : String :=
  "\"tags\":{\"idempotency-key\":[\"" ++ Codec.Base64Url.encodeString key.toUTF8 ++ "\"]}"

/-- SES publishes to SNS, which posts an envelope whose `Message` is the payload as a string. -/
private def wrapped (message : String) : String :=
  "{\"Type\":\"Notification\",\"TopicArn\":\"arn:aws:sns:eu-west-1:1:bounces\"," ++
  "\"Message\":" ++ (Lean.Json.str message).compress ++ "}"

private def sesBounce : String :=
  wrapped ("{\"notificationType\":\"Bounce\",\"bounce\":{\"bounceType\":\"Permanent\"," ++
    "\"bounceSubType\":\"General\",\"bouncedRecipients\":[" ++
    "{\"emailAddress\":\"one@example.com\",\"diagnosticCode\":\"smtp; 550 5.1.1\"}," ++
    "{\"emailAddress\":\"two@example.com\"}]}," ++
    "\"mail\":{\"messageId\":\"m-1\"," ++ sesTag "attempt:a-2" ++ "}}")

private def sesTransient : String :=
  wrapped ("{\"eventType\":\"Bounce\",\"bounce\":{\"bounceType\":\"Transient\"," ++
    "\"bounceSubType\":\"MailboxFull\",\"bouncedRecipients\":" ++
    "[{\"emailAddress\":\"busy@example.com\"}]},\"mail\":{\"messageId\":\"m-2\"}}")

private def sesComplaint : String :=
  wrapped ("{\"eventType\":\"Complaint\",\"complaint\":{\"complaintFeedbackType\":\"abuse\"," ++
    "\"complainedRecipients\":[{\"emailAddress\":\"cross@example.com\"}]}," ++
    "\"mail\":{\"messageId\":\"m-3\"}}")

private def sesDelivery : String :=
  wrapped "{\"eventType\":\"Delivery\",\"mail\":{\"messageId\":\"m-4\"}}"

private def addressesOf (events : List DeliveryEvent) : List String :=
  events.map (·.address.render)

private def failuresOf (events : List DeliveryEvent) : List DeliveryFailure :=
  events.map (·.failure)

def parserChecks : List (String × Bool) :=
  let bounce := Postmark.deliveryEvents postmarkBounce
  let ses := Ses.deliveryEvents sesBounce
  [ ("postmark: a hard bounce is permanent (AUTH-12.1)",
      failuresOf bounce == [.hardBounce]),
    ("postmark: the bounced address is the one reported",
      (bounce.head?.map (·.address.normalise.localPart)) == some "gone"),
    ("postmark: the idempotency key names the attempt the mail belonged to (AUTH-10.4)",
      (bounce.head?.bind (·.reference)) == some "attempt:a-1"),
    ("postmark: the provider's own words are kept for the operator",
      (bounce.head?.map fun e => !e.detail.isEmpty) == some true),
    ("postmark: a transient bounce is counted, not suppressed",
      failuresOf (Postmark.deliveryEvents postmarkTransient) == [.softBounce]),
    ("postmark: a spam complaint is permanent",
      failuresOf (Postmark.deliveryEvents postmarkComplaint) == [.spamComplaint]),
    ("postmark: a record type that is not a failure yields nothing",
      (Postmark.deliveryEvents postmarkDelivery).isEmpty),
    ("postmark: a payload that is not JSON yields nothing rather than failing",
      (Postmark.deliveryEvents "not json at all").isEmpty),
    ("ses: the SNS envelope is unwrapped and every recipient reported",
      addressesOf ses == ["one@example.com", "two@example.com"]),
    ("ses: a permanent bounce is permanent for all of them",
      failuresOf ses == [.hardBounce, .hardBounce]),
    ("ses: the idempotency key survives the tag alphabet (AUTH-10.4)",
      (ses.head?.bind (·.reference)) == some "attempt:a-2"),
    ("ses: a transient bounce is counted, not suppressed",
      failuresOf (Ses.deliveryEvents sesTransient) == [.softBounce]),
    ("ses: a complaint is permanent",
      failuresOf (Ses.deliveryEvents sesComplaint) == [.spamComplaint]),
    ("ses: an event that is not a failure yields nothing",
      (Ses.deliveryEvents sesDelivery).isEmpty),
    ("ses: an unwrapped payload is read as itself",
      failuresOf (Ses.deliveryEvents
        "{\"eventType\":\"Complaint\",\"complaint\":{\"complainedRecipients\":[{\"emailAddress\":\"x@example.com\"}]}}")
        == [.spamComplaint]) ]

/-! ## What suppression does -/

initialize clockRef : IO.Ref Timestamp ← IO.mkRef ⟨1700000000⟩
initialize drawCounter : IO.Ref Nat ← IO.mkRef 0
initialize sentRef : IO.Ref (List OutboundEmail) ← IO.mkRef []

instance : Clock IO where
  now := clockRef.get

instance : RandomBytes IO where
  draw count := do
    let index ← drawCounter.modifyGet fun n => (n, n + 1)
    pure (.ok ((Crypto.Sha256.hashUtf8 s!"suppression-seed-{index}").extract 0 count))

def capturing : EmailTransport IO where
  send mail := do
    sentRef.modify (· ++ [mail])
    pure (.ok ⟨mail.idempotencyKey⟩)

private def address (raw : String) : EmailAddress := (EmailAddress.parse raw).toOption.getD default

def peppers : PepperRing :=
  { current := { keyId := ⟨"pepper-1"⟩, secret := Crypto.Sha256.hashUtf8 "test pepper" } }

def tenant : TenantId := ⟨"acme"⟩

private def portsOn (db : SQLite) : Ports IO :=
  { store := Sqlite.store db
    transport := capturing
    responsePolicy := SignInResponsePolicy.silent IO
    limiter := RateLimiter.unlimited IO
    responseFloor := ResponseFloor.immediate IO
    peppers }

private def config : TenantConfig tenant :=
  { displayName := "Acme"
    baseUrl := ⟨"https://auth.example.com"⟩
    sendingIdentity :=
      { address := address "sign-in@auth.example.com", displayName := "Acme sign-in" }
    signupPolicy := .unrestricted }

private def sentCount : IO Nat := do pure (← sentRef.get).length

def checks : IO (List (String × Bool)) := do
  clockRef.set ⟨1700000000⟩
  sentRef.set []
  let db ← Sqlite.openInMemory
  let ports := portsOn db
  let gone := address "gone@example.com"
  let busy := address "busy@example.com"

  -- A working address, so there is something to compare against.
  let (_, _) ← begin ports config gone {}
  let sentBefore ← sentCount

  let bounced ← ingestDelivery (tenant := tenant) ports
    { address := gone, failure := .hardBounce, detail := "550 5.1.1" }
  let (_, response) ← begin ports config gone {}
  let sentAfter ← sentCount
  let audited ← ports.store.auditEntries tenant

  -- Transient failures are counted and nothing more.
  let softOnce ← ingestDelivery (tenant := tenant) ports
    { address := busy, failure := .softBounce, detail := "mailbox full" }
  let softTwice ← ingestDelivery (tenant := tenant) ports
    { address := busy, failure := .softBounce, detail := "mailbox full" }
  let (_, _) ← begin ports config busy {}
  let sentToBusy ← sentCount

  -- Inviting a suppressed address: the invitation is made and the client is told nobody will
  -- ever receive it.
  let invited ← createInvitation ports config gone ⟨"{}"⟩
  let sentToInvited ← sentCount

  -- The report, and then clearing.
  let report ← deliveryReport (tenant := tenant) ports (minimumFailures := 2)
  let stillSuppressed ← suppressed (tenant := tenant) ports gone
  clearSuppression (tenant := tenant) ports gone
  let afterClearing ← suppressed (tenant := tenant) ports gone
  let (_, _) ← begin ports config gone {}
  let sentAfterClearing ← sentCount

  -- And suppression the client asked for, which the providers had nothing to do with.
  let byClient ← suppressAddress (tenant := tenant) ports busy "asked us to stop"

  pure
    [ ("suppression: a hard bounce suppresses the address (AUTH-12.1)",
        bounced.suppressedBy == some .hardBounce),
      ("suppression: no mail is sent to a suppressed address (AUTH-12.3)",
        sentBefore == 1 && sentAfter == 1),
      ("suppression: the person is told what the policy says, not what happened (AUTH-14.2)",
        response.message == .checkYourMail),
      ("suppression: the true outcome is audited all the same (AUTH-14.2.6)",
        audited.any fun entry =>
          match entry.event with
          | .signInRejected .addressSuppressed => true
          | _ => false),
      ("suppression: the log says which address stopped receiving mail",
        audited.any fun entry =>
          match entry.event with
          | .addressSuppressed found .hardBounce => found == gone.normalise
          | _ => false),
      ("suppression: transient failures are counted and do not suppress (AUTH-12.5)",
        !softOnce.suppressed && softTwice.failures == 2 && sentToBusy == 2),
      ("suppression: an invitation to a suppressed address is not sent (AUTH-12.3)",
        sentToInvited == 2),
      ("suppression: and the client is told why, permanently (AUTH-10.3)",
        (invited.map fun issued =>
          match issued.delivery with
          | .error e => e == .addressSuppressed && e.isPermanent
          | .ok _ => false) == some true),
      ("suppression: the report names the addresses worth telling the client about (AUTH-12.5)",
        report.map (·.address.localPart) == ["busy", "gone"]),
      ("suppression: clearing lets the address receive mail again (AUTH-12.4)",
        stillSuppressed && !afterClearing && sentAfterClearing == 3),
      ("suppression: the client can suppress an address the providers never mentioned",
        byClient.suppressedBy == some .client) ]

end Tests.Suppression
