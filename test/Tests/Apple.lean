/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import AuthenticationOidc

/-!
Apple's three departures from every other provider (AUTH-6.9).

The client secret is minted rather than held, the callback arrives as a cross-site `POST`, and the
address may be a relay that must not answer a domain allowlist. The first is here; the third is a
theorem in `Tests.Policy`, because it is a claim about a pure function.
-/

namespace Tests.Apple
open Authentication Authentication.Oidc

private def keyPem : String := include_str "../fixtures/apple-key.p8"

private def now : Timestamp := ⟨1780000000⟩

private def provider : ProviderConfig :=
  { id := ⟨"apple"⟩
    issuer := "https://appleid.apple.com"
    clientId := "com.example.service"
    credentials := .signingKey "TEAM123456" "KEY7890AB" (.external "unused")
    formPost := true
    scopes := ["openid", "email", "name"] }

private def discovery : Discovery :=
  { issuer := provider.issuer
    authorizationEndpoint := provider.issuer ++ "/auth/authorize"
    tokenEndpoint := provider.issuer ++ "/auth/token"
    jwksUri := provider.issuer ++ "/auth/keys" }

private def decodePart (part : String) : String :=
  match Leancrypto.Codec.Base64Url.decodeString part with
  | some bytes => (String.fromUTF8? bytes).getD ""
  | none => ""

def checks : IO (List (String × Bool)) := do
  let minted ← mintAssertion provider discovery "TEAM123456" "KEY7890AB" keyPem.toUTF8 now
  let parts := (minted.toOption.getD "").splitOn "."
  let header := decodePart (parts[0]?.getD "")
  let payload := decodePart (parts[1]?.getD "")
  let signature := parts[2]?.getD ""
  let rubbish ← mintAssertion provider discovery "TEAM123456" "KEY7890AB" "not a key".toUTF8 now
  let refused := match rubbish with | .error _ => true | .ok _ => false
  pure
    [ ("apple: a client secret is minted from the key", minted.toOption.isSome)
    , ("apple: it is a three-part compact JWS", parts.length == 3)
    , ("apple: signed ES256, naming the key (AUTH-6.9)",
        header == "{\"alg\":\"ES256\",\"kid\":\"KEY7890AB\"}")
    , ("apple: issued by the team, for the provider, about the client",
        (payload.splitOn "\"iss\":\"TEAM123456\"").length == 2
          && (payload.splitOn "\"aud\":\"https://appleid.apple.com\"").length == 2
          && (payload.splitOn "\"sub\":\"com.example.service\"").length == 2)
    , ("apple: with a bounded lifetime rather than none",
        (payload.splitOn ("\"exp\":" ++ toString (now.advance assertionLifetime).epochSeconds)).length == 2)
    , ("apple: an ES256 signature is 64 bytes, raw r and s (RFC 7518)",
        (Leancrypto.Codec.Base64Url.decodeString signature).map (·.size) == some 64)
    , ("apple: a key that is not one is refused rather than signed with", refused) ]

/-- The authorization request and the cookie both change shape for a provider that posts back. -/
def formPostChecks : IO (List (String × Bool)) := do
  let base : BaseUrl := ⟨"https://auth.example.test"⟩
  let tenant : TenantId := ⟨"acme"⟩
  let posting := stateCookie base tenant true "value" now
  let redirecting := stateCookie base tenant false "value" now
  pure
    [ ("apple: a form_post provider's state cookie is SameSite=None (AUTH-6.9)",
        posting.sameSite == .none)
    , ("apple: and still Secure and HttpOnly, which None requires",
        posting.secure && posting.httpOnly)
    , ("apple: every other provider keeps Lax (AUTH-5.2.4)", redirecting.sameSite == .lax) ]

end Tests.Apple
