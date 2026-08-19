#!/bin/bash
#
# Regenerates the SNS fixtures: a key, a self-signed certificate, and two messages signed over the
# canonical string AWS specifies. Run as `make-sns-fixtures.sh <dir>`; the outputs are committed,
# and the private key is discarded, because nothing needs to sign again.
#
# The point of signing here rather than in Lean is that nothing in that library can sign. A
# fixture the verifier's own code produced would prove only that it agrees with itself.
#
# Two things will waste an afternoon if forgotten:
#
#   - The canonical string ends in a newline, and `$(...)` strips trailing newlines, so it must
#     reach openssl through a file rather than a shell variable.
#   - Lake does not track `include_str` inputs, so a test reading these will keep its old copy
#     until something else in that module changes. Touch the test file after regenerating.
#
set -euo pipefail
out="$1"
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT

mkdir -p "$out"

openssl req -x509 -newkey rsa:2048 -keyout "$work/key.pem" -out "$out/sns-certificate.pem" \
  -days 36500 -nodes -subj "/CN=sns.eu-west-1.amazonaws.com" 2>/dev/null

# JSON-escapes a string for embedding as a JSON string value.
esc() { printf '%s' "$1" | sed -e 's/\\/\\\\/g' -e 's/"/\\"/g'; }

# Signs the file at $1. The canonical string ends in a newline, and command substitution strips
# trailing newlines, so it must never travel through a shell variable.
sign() { openssl dgst -sha256 -sign "$work/key.pem" "$1" | openssl base64 -A; }

ARN="arn:aws:sns:eu-west-1:123456789012:auth-bounces"
CERT="https://sns.eu-west-1.amazonaws.com/SimpleNotificationService-fixture.pem"
TS="2026-08-19T10:00:00.000Z"

# A Notification carrying an SES permanent bounce for two recipients.
INNER='{"notificationType":"Bounce","bounce":{"bounceType":"Permanent","bounceSubType":"General","bouncedRecipients":[{"emailAddress":"one@example.com","diagnosticCode":"smtp; 550 5.1.1 user unknown"},{"emailAddress":"two@example.com"}]},"mail":{"messageId":"0100018f-1","tags":{"idempotency-key":["YXR0ZW1wdDphLTE"]}}}'
ID="8f1b2c3d-0000-4000-8000-000000000001"
printf 'Message\n%s\nMessageId\n%s\nTimestamp\n%s\nTopicArn\n%s\nType\nNotification\n' \
  "$INNER" "$ID" "$TS" "$ARN" > "$work/sts1"
SIG=$(sign "$work/sts1")
cat > "$out/sns-notification.json" <<JSON
{"Type":"Notification","MessageId":"$ID","TopicArn":"$ARN","Message":"$(esc "$INNER")","Timestamp":"$TS","SignatureVersion":"2","Signature":"$SIG","SigningCertURL":"$CERT","UnsubscribeURL":"https://sns.eu-west-1.amazonaws.com/?Action=Unsubscribe"}
JSON

# A SubscriptionConfirmation, whose signed field list differs.
CID="8f1b2c3d-0000-4000-8000-000000000002"
TOKEN="2336412f37fb687f5d51e6e2425cf3f0f7f0e5b0"
SUB="https://sns.eu-west-1.amazonaws.com/?Action=ConfirmSubscription&Token=$TOKEN"
CMSG="You have chosen to subscribe to the topic $ARN.\\nTo confirm the subscription, visit the SubscribeURL included in this message."
CMSG_RAW=$(printf 'You have chosen to subscribe to the topic %s.\nTo confirm the subscription, visit the SubscribeURL included in this message.' "$ARN")
printf 'Message\n%s\nMessageId\n%s\nSubscribeURL\n%s\nTimestamp\n%s\nToken\n%s\nTopicArn\n%s\nType\nSubscriptionConfirmation\n' \
  "$CMSG_RAW" "$CID" "$SUB" "$TS" "$TOKEN" "$ARN" > "$work/sts2"
CSIG=$(sign "$work/sts2")
cat > "$out/sns-confirmation.json" <<JSON
{"Type":"SubscriptionConfirmation","MessageId":"$CID","Token":"$TOKEN","TopicArn":"$ARN","Message":"$CMSG","SubscribeURL":"$SUB","Timestamp":"$TS","SignatureVersion":"2","Signature":"$CSIG","SigningCertURL":"$CERT"}
JSON

echo "wrote $out/{sns-certificate.pem,sns-notification.json,sns-confirmation.json}"
