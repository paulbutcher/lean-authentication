/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import AuthenticationPostmark
import AuthenticationSes
import AuthenticationSqlite

/-!
Establishing that a delivery event came from the provider (AUTH-12.1.1).

The SNS fixtures are real: a 2048-bit key and a self-signed certificate, and two messages signed
with `openssl` over the canonical string AWS specifies. Nothing in this repository can produce an
RSA signature, which is the point. The verifier is checked against bytes it did not make, and the
canonical string is checked by the only means available, which is that a signature over an
independently built one verifies at all.

The negative cases matter more than the positive one and are the reason the fixtures exist: a
verifier that returns `true` for everything passes the positive case.
-/

namespace Tests.Webhooks
open Authentication

private def certificate : String := include_str "../fixtures/sns-certificate.pem"
private def notification : String := include_str "../fixtures/sns-notification.json"
private def confirmation : String := include_str "../fixtures/sns-confirmation.json"

private def topic : String := "arn:aws:sns:eu-west-1:123456789012:auth-bounces"

initialize confirmedRef : IO.Ref (List String) ← IO.mkRef []
initialize fetchedRef : IO.Ref (List String) ← IO.mkRef []

/-- Stands in for the fetch, and records what was asked for, so a check can tell "refused before
fetching" from "fetched and then refused". -/
private def subscription (topics : List String := [topic]) : Ses.Subscription IO :=
  { topics
    certificate := fun url => do
      fetchedRef.modify (· ++ [url])
      pure (some certificate)
    confirm := fun url => do
      confirmedRef.modify (· ++ [url])
      pure true }

/-- Swaps one substring for another, to damage a signed message in one place. -/
private def replacing (text pattern replacement : String) : String :=
  String.intercalate replacement (text.splitOn pattern)

private def outcomeOf (result : WebhookOutcome) : String :=
  match result with
  | .ingest events => s!"ingest:{events.length}"
  | .accepted => "accepted"
  | .rejected => "rejected"

def snsChecks : IO (List (String × Bool)) := do
  fetchedRef.set []
  confirmedRef.set []
  let endpoint := Ses.endpoint (subscription)
  let tenant : TenantId := ⟨"acme"⟩
  let noHeaders (_ : String) : Option String := none
  let accept (body : String) : IO WebhookOutcome := endpoint.accept tenant noHeaders body

  let good ← accept notification
  let events := match good with | .ingest events => events | _ => []

  -- The signature covers the message, so moving an address inside it must break it.
  let tampered ← accept (replacing notification "one@example.com" "attacker@example.com")
  -- And covers the topic, so a substituted one cannot verify either. What this cannot catch is a
  -- message correctly signed by SNS for somebody else's topic, which is the next check.
  let retopiced ← accept (replacing notification topic "arn:aws:sns:eu-west-1:1:elsewhere")

  let confirmed ← accept confirmation
  let visited ← confirmedRef.get

  -- Verified, correctly signed, and from a topic this endpoint was not configured for. Anyone
  -- with an AWS account can subscribe someone else's endpoint to a topic of their own, so a
  -- signature alone establishes only that SNS sent it.
  let foreign := Ses.endpoint (subscription (topics := ["arn:aws:sns:eu-west-1:1:someone-else"]))
  let wrongTopic ← foreign.accept tenant noHeaders notification

  -- Refused before the fetch: the certificate URL decides where a key comes from, so a payload
  -- naming a host of its own must not be asked about.
  fetchedRef.set []
  let elsewhere ← accept (replacing notification
    "https://sns.eu-west-1.amazonaws.com/SimpleNotificationService-fixture.pem"
    "https://sns.eu-west-1.amazonaws.com.evil.test/key.pem")
  let fetchedAfterBadUrl ← fetchedRef.get

  let userinfo ← accept (replacing notification
    "https://sns.eu-west-1.amazonaws.com/SimpleNotificationService-fixture.pem"
    "https://sns.eu-west-1.amazonaws.com@evil.test/key.pem")
  let legacyVersion ← accept (replacing notification "\"SignatureVersion\":\"2\""
    "\"SignatureVersion\":\"1\"")
  let garbage ← accept "not json at all"

  pure
    [ ("sns: a genuinely signed notification verifies and yields its events (AUTH-12.1.1)",
        outcomeOf good == "ingest:2"),
      ("sns: and the events are the ones the payload carried",
        events.map (·.address.render) == ["one@example.com", "two@example.com"]
          && events.all (·.failure == .hardBounce)),
      ("sns: a message altered after signing is refused",
        outcomeOf tampered == "rejected"),
      ("sns: so is one whose topic was substituted",
        outcomeOf retopiced == "rejected"),
      ("sns: a subscription confirmation verifies under its own field list and is answered",
        outcomeOf confirmed == "accepted" && visited.length == 1),
      ("sns: a valid signature for a topic this endpoint does not serve is refused",
        outcomeOf wrongTopic == "rejected"),
      ("sns: a certificate host the payload chose is refused, and never fetched",
        outcomeOf elsewhere == "rejected" && fetchedAfterBadUrl.isEmpty),
      ("sns: userinfo in the certificate URL does not disguise the host",
        outcomeOf userinfo == "rejected"),
      ("sns: signature version 1 is refused rather than verified with SHA-1",
        outcomeOf legacyVersion == "rejected"),
      ("sns: a body that is not JSON is refused rather than failing",
        outcomeOf garbage == "rejected") ]

def postmarkChecks : IO (List (String × Bool)) := do
  let credentials : Postmark.Credentials := { username := "hook", password := "s3cret" }
  let endpoint := Postmark.endpoint (m := IO) credentials
  let tenant : TenantId := ⟨"acme"⟩
  let bounce :=
    "{\"RecordType\":\"Bounce\",\"Type\":\"HardBounce\",\"Email\":\"gone@example.com\"," ++
    "\"Description\":\"550\"}"
  let withHeader (value : Option String) (field : String) : Option String :=
    if field == "authorization" then value else none
  let right := "Basic " ++ Codec.Base64.encodeString "hook:s3cret".toUTF8

  let admitted ← endpoint.accept tenant (withHeader (some right)) bounce
  let missing ← endpoint.accept tenant (withHeader none) bounce
  let wrong ← endpoint.accept tenant
    (withHeader (some ("Basic " ++ Codec.Base64.encodeString "hook:wrong".toUTF8))) bounce
  let unencoded ← endpoint.accept tenant (withHeader (some "Basic hook:s3cret")) bounce

  pure
    [ ("postmark: the configured credentials admit the payload (AUTH-12.1.1)",
        outcomeOf admitted == "ingest:1"),
      ("postmark: a request with no credentials is refused",
        outcomeOf missing == "rejected"),
      ("postmark: so is one with the wrong password",
        outcomeOf wrong == "rejected"),
      ("postmark: and one that did not encode them",
        outcomeOf unencoded == "rejected") ]

end Tests.Webhooks
