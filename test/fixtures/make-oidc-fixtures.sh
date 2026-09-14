#!/usr/bin/env bash
# Regenerates the OIDC signing key and the JWKS that publishes it. The tests mint ID tokens with
# the private key and verify them against the JWKS, so the pair has to be built together.
set -euo pipefail
cd "$(dirname "$0")"

openssl genrsa -out oidc-key.pem 2048 2>/dev/null

b64url() { base64 -w0 | tr '+/' '-_' | tr -d '='; }

modulus=$(openssl rsa -in oidc-key.pem -noout -modulus | sed 's/^Modulus=//')
n=$(printf '%s' "$modulus" | xxd -r -p 2>/dev/null | b64url || printf '%s' "$modulus" | perl -ne 's/([0-9A-Fa-f]{2})/print chr hex $1/ge' | b64url)

cat > oidc-jwks.json <<JSON
{"keys":[{"kty":"RSA","use":"sig","alg":"RS256","kid":"oidc-test-1","n":"$n","e":"AQAB"}]}
JSON

echo "wrote oidc-key.pem and oidc-jwks.json"

# Apple ships its signing key as a `.p8`, which is PEM-armoured PKCS#8 over a P-256 key. The
# tests mint a client secret with it; nothing verifies the signature here, so only the private
# half is needed.
openssl genpkey -algorithm EC -pkeyopt ec_paramgen_curve:P-256 -out apple-key.p8 2>/dev/null
echo "wrote apple-key.p8"
