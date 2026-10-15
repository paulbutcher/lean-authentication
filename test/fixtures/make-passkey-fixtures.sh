#!/bin/bash
#
# Regenerates the passkey assertion fixture: a key, an `authenticatorData` laid out by hand, a
# `clientDataJSON`, and a signature over the two of them. Run as `make-passkey-fixtures.sh <dir>`;
# the outputs are committed, and the private key is kept because nothing else can produce another
# signature under the same public key.
#
# The point of assembling the bytes here rather than in Lean is the point of the SNS script: a
# fixture the verifier's own code laid out would prove only that it agrees with itself. The offsets
# below are read off the WebAuthn specification, not off this library.
#
set -euo pipefail
out="$1"
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT

rp="passkey.example.test"
origin="https://passkey.example.test"
challenge="dGVzdC1jaGFsbGVuZ2UtdmFsdWU"

b64url() { base64 -w0 "$1" | tr '+/' '-_' | tr -d '='; }

openssl ecparam -name prime256v1 -genkey -noout -out "$out/passkey-key.pem" 2>/dev/null

# rpIdHash (32) || flags (1) || signCount (4). `0x01` is user presence and nothing else: no
# attested credential data, which is what an assertion carries.
printf '%s' "$rp" | openssl dgst -sha256 -binary > "$work/authdata"
printf '\x01\x00\x00\x00\x01' >> "$work/authdata"

printf '%s' \
  "{\"type\":\"webauthn.get\",\"challenge\":\"$challenge\",\"origin\":\"$origin\",\"crossOrigin\":false}" \
  > "$work/clientdata"

# The signing input is `authenticatorData || SHA-256(clientDataJSON)`, in that order.
cat "$work/authdata" > "$work/signinput"
openssl dgst -sha256 -binary "$work/clientdata" >> "$work/signinput"

openssl dgst -sha256 -sign "$out/passkey-key.pem" -out "$work/signature" "$work/signinput"
openssl pkey -in "$out/passkey-key.pem" -pubout -outform DER -out "$work/spki"

cat > "$out/passkey-assertion.json" <<JSON
{
  "relyingPartyId": "$rp",
  "origin": "$origin",
  "challenge": "$challenge",
  "authenticatorData": "$(b64url "$work/authdata")",
  "clientDataJSON": "$(b64url "$work/clientdata")",
  "signature": "$(b64url "$work/signature")",
  "publicKey": "$(b64url "$work/spki")"
}
JSON
