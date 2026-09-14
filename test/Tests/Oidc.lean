/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import AuthenticationOidc
import Authentication.Instances

/-!
The OIDC core: discovery (AUTH-6.4), ID token validation (AUTH-6.5) and the `nonce` of AUTH-6.3.

The tokens here are real ones. `test/fixtures/oidc-key.pem` signs them and
`test/fixtures/oidc-jwks.json` publishes the matching public key, so a check that a token verifies
is a check that this library's reading of the two agrees with OpenSSL's.
-/

namespace Tests.Oidc
open Authentication Authentication.Oidc

private def privateKeyPem : String := include_str "../fixtures/oidc-key.pem"
private def jwksJson : String := include_str "../fixtures/oidc-jwks.json"

private def issuer : String := "https://issuer.example.com"
private def clientId : String := "client-abc"

private def provider : ProviderConfig :=
  { id := ⟨"test"⟩, issuer, clientId, credentials := .clientSecret (.external "unused") }

private def discovery : Discovery :=
  { issuer
    authorizationEndpoint := issuer ++ "/authorize"
    tokenEndpoint := issuer ++ "/token"
    jwksUri := issuer ++ "/jwks" }

private def now : Timestamp := ⟨1780000000⟩

private def b64 (bytes : ByteArray) : String := Leancrypto.Codec.Base64Url.encodeString bytes

/-- Assembles a compact JWS by hand, which is all a token is: two base64url JSON parts, and a
signature over the text of both with the dot between them. -/
private def mint (header payload : String) : IO (Option String) := do
  match ← Jose.Libcrypto.PreparedKey.ofPem privateKeyPem with
  | .error _ => pure none
  | .ok key =>
    let signingInput := b64 header.toUTF8 ++ "." ++ b64 payload.toUTF8
    match ← Jose.Backend.libcrypto.sign .rs256 key signingInput.toUTF8 with
    | .error _ => pure none
    | .ok signature => pure (some (signingInput ++ "." ++ b64 signature))

private def header : String := "{\"alg\":\"RS256\",\"typ\":\"JWT\",\"kid\":\"oidc-test-1\"}"

/-- The claims a provider sends, with every part a check needs to vary exposed as an argument. -/
private def claims (iss aud sub nonce : String) (exp : Int) (extra : String := "") : String :=
  "{\"iss\":\"" ++ iss ++ "\",\"aud\":\"" ++ aud ++ "\",\"sub\":\"" ++ sub ++
    "\",\"nonce\":\"" ++ nonce ++ "\",\"exp\":" ++ toString exp ++ ",\"iat\":" ++
    toString (exp - 300) ++ extra ++ "}"

private def goodClaims (extra : String := "") : String :=
  claims issuer clientId "subject-42" "the-nonce" (now.epochSeconds + 600) extra

private def keySet : IO (Option (Jose.KeySet Jose.Backend.libcrypto)) := do
  match Jose.Jwks.parse {} jwksJson with
  | .error _ => pure none
  | .ok set =>
    match ← Jose.KeySet.ofJwks Jose.Backend.libcrypto set with
    | .error _ => pure none
    | .ok prepared => pure (some prepared)

private def verify (payload : String) (nonce : String := "the-nonce") :
    IO (Except OidcError ProviderAnswer) := do
  match ← keySet, ← mint header payload with
  | some keys, some token => validate provider discovery keys nonce token now
  | _, _ => pure (.error (.badDocument "fixture"))

private def rejected : Except OidcError ProviderAnswer → Bool
  | .error _ => true
  | .ok _ => false

def checks : IO (List (String × Bool)) := do
  let valid ← verify (goodClaims ",\"email\":\"person@example.com\",\"email_verified\":true")
  let unverified ← verify (goodClaims ",\"email\":\"person@example.com\",\"email_verified\":false")
  let silent ← verify (goodClaims ",\"email\":\"person@example.com\"")
  let stringy ← verify (goodClaims ",\"email\":\"p@example.com\",\"email_verified\":\"true\"")
  let hosted ← verify (goodClaims ",\"email\":\"p@example.com\",\"email_verified\":true,\"hd\":\"example.com\"")
  let wrongNonce ← verify (goodClaims) "a-different-nonce"
  let noNonce ← verify (claims issuer clientId "subject-42" "" (now.epochSeconds + 600))
  let wrongAudience ← verify (claims issuer "someone-else" "s" "the-nonce" (now.epochSeconds + 600))
  let wrongIssuer ← verify (claims "https://evil.example" clientId "s" "the-nonce" (now.epochSeconds + 600))
  let expired ← verify (claims issuer clientId "s" "the-nonce" (now.epochSeconds - 600))
  let noSubject ← verify
    ("{\"iss\":\"" ++ issuer ++ "\",\"aud\":\"" ++ clientId ++
      "\",\"nonce\":\"the-nonce\",\"exp\":" ++ toString (now.epochSeconds + 600) ++ "}")
  -- Alg confusion: the token asks to be checked as HMAC, with the public key as the secret.
  let hmacToken ← verify (goodClaims)
  let confused ← match ← keySet with
    | none => pure (.error (.badDocument "fixture"))
    | some keys =>
      let signingInput := b64 "{\"alg\":\"HS256\",\"kid\":\"oidc-test-1\"}".toUTF8 ++ "." ++
        b64 (goodClaims).toUTF8
      validate provider discovery keys "the-nonce" (signingInput ++ "." ++ b64 "x".toUTF8) now
  pure
    [ ("oidc: a token signed by the provider's key validates",
        (valid.toOption.map (·.identity.subject)) == some "subject-42")
    , ("oidc: the issuer is the identity's, not the token's word for it",
        (valid.toOption.map (·.identity.issuer)) == some issuer)
    , ("oidc: a verified address is reported verified",
        (valid.toOption.map (·.addressVerified)) == some true)
    , ("oidc: email_verified false is not verified (AUTH-6.7)",
        (unverified.toOption.map (·.addressVerified)) == some false)
    , ("oidc: a provider that says nothing has not said yes",
        (silent.toOption.map (·.addressVerified)) == some false)
    , ("oidc: email_verified sent as a string is read",
        (stringy.toOption.map (·.addressVerified)) == some true)
    , ("oidc: hd is carried as supporting evidence (AUTH-6.9)",
        (hosted.toOption.bind (·.hostedDomain)) == some "example.com")
    , ("oidc: the address is parsed off the token",
        (valid.toOption.bind (·.address.map (·.render))) == some "person@example.com")
    , ("oidc: a token echoing the wrong nonce is refused (AUTH-6.3)", rejected wrongNonce)
    , ("oidc: a token with no nonce is refused", rejected noNonce)
    , ("oidc: a token for another audience is refused (AUTH-6.5)", rejected wrongAudience)
    , ("oidc: a token from another issuer is refused", rejected wrongIssuer)
    , ("oidc: an expired token is refused", rejected expired)
    , ("oidc: a token with no subject is refused (AUTH-6.6)", rejected noSubject)
    , ("oidc: an HS256 token is refused whatever its signature (AUTH-6.5)", rejected confused)
    , ("oidc: the fixture pair is what makes the refusals meaningful", hmacToken.toOption.isSome) ]

/-- Discovery, which is pure once the document is in hand. -/
def discoveryChecks : List (String × Bool) :=
  let document := "{\"issuer\":\"" ++ issuer ++ "\",\"authorization_endpoint\":\"" ++ issuer ++
    "/authorize\",\"token_endpoint\":\"" ++ issuer ++ "/token\",\"jwks_uri\":\"" ++ issuer ++
    "/jwks\"}"
  let refused (result : Except OidcError Discovery) := match result with
    | .error _ => true
    | .ok _ => false
  [ ("oidc: a discovery document is read",
      (readDiscovery issuer document).toOption.map (·.jwksUri) == some (issuer ++ "/jwks"))
  , ("oidc: a document naming another issuer is refused",
      refused (readDiscovery "https://elsewhere.example" document))
  , ("oidc: a document missing an endpoint is refused",
      refused (readDiscovery issuer ("{\"issuer\":\"" ++ issuer ++ "\"}")))
  , ("oidc: the well-known URL follows the issuer's trailing slash",
      wellKnownUrl "https://a.example/" == "https://a.example/.well-known/openid-configuration")
  , ("oidc: an issuer carrying a path keeps it",
      wellKnownUrl "https://a.example/tenant" ==
        "https://a.example/tenant/.well-known/openid-configuration") ]


/-- Answers every request with the same document and counts how many were made, which is what the
cache and the refetch limit are about. -/
private def counting (body : String) (seen : IO.Ref Nat) : Fetch.Http IO where
  send _ := do
    seen.modify (· + 1)
    pure (.ok { status := 200, headers := [], body := body.toUTF8 })

def cacheChecks : IO (List (String × Bool)) := do
  let held ← IO.mkRef 0
  let cached ← keys (counting jwksJson held) { defaultFreshness := Duration.hours 1 }
  let _ ← cached.jwks discovery false
  let afterFirst ← held.get
  let _ ← cached.jwks discovery false
  let afterSecond ← held.get

  -- A cache that has gone stale fetches again without being asked to refresh.
  let stale ← IO.mkRef 0
  let expiring ← keys (counting jwksJson stale) { defaultFreshness := ⟨0⟩ }
  let _ ← expiring.jwks discovery false
  let _ ← expiring.jwks discovery false
  let afterStale ← stale.get

  -- An unknown `kid` asking to refresh straight after a fetch is refused, and costs no request.
  let throttled ← IO.mkRef 0
  let limited ← keys (counting jwksJson throttled)
    { defaultFreshness := Duration.hours 1, minRefetchInterval := Duration.minutes 5 }
  let _ ← limited.jwks discovery false
  let refused ← limited.jwks discovery true
  let afterThrottle ← throttled.get

  -- With no interval to wait out, the same refresh is served.
  let open' ← IO.mkRef 0
  let unlimited ← keys (counting jwksJson open')
    { defaultFreshness := Duration.hours 1, minRefetchInterval := ⟨0⟩ }
  let _ ← unlimited.jwks discovery false
  let allowed ← unlimited.jwks discovery true
  let afterOpen ← open'.get

  let document := "{\"issuer\":\"" ++ issuer ++ "\",\"authorization_endpoint\":\"" ++ issuer ++
    "/authorize\",\"token_endpoint\":\"" ++ issuer ++ "/token\",\"jwks_uri\":\"" ++ issuer ++
    "/jwks\"}"
  let discovered ← IO.mkRef 0
  let found ← (metadata (counting document discovered)).discover provider

  pure
    [ ("oidc: the first ask for a key set fetches it", afterFirst == 1)
    , ("oidc: the second is served from cache (AUTH-6.4)", afterSecond == 1)
    , ("oidc: a stale key set is fetched again", afterStale == 2)
    , ("oidc: a refetch too soon after the last is refused (AUTH-6.4)",
        match refused with | .error .refetchThrottled => true | _ => false)
    , ("oidc: and it costs no outbound request", afterThrottle == 1)
    , ("oidc: a refetch past the interval is served", allowed.toOption.isSome && afterOpen == 2)
    , ("oidc: the metadata port reads the document it fetched",
        (found.toOption.map (·.tokenEndpoint)) == some (issuer ++ "/token")) ]

/--
A token naming a key nobody published (AUTH-6.4).

This is the case a stranger controls: the `kid` comes off a token anybody can post. So the budget
it can spend has to be one refetch and no more, and none at all while the last fetch is recent.
-/
def refetchChecks : IO (List (String × Bool)) := do
  let elsewhere := jwksJson.replace "oidc-test-1" "a-key-nobody-has"
  let token ← mint header (goodClaims)

  let eager ← IO.mkRef 0
  let open' ← keys (counting elsewhere eager)
    { defaultFreshness := Duration.hours 1, minRefetchInterval := ⟨0⟩ }
  let openOutcome ← match token with
    | none => pure (.error (.badDocument "fixture"))
    | some t => verifyIdToken open' provider discovery "the-nonce" t now
  let eagerCount ← eager.get

  let held ← IO.mkRef 0
  let limited ← keys (counting elsewhere held)
    { defaultFreshness := Duration.hours 1, minRefetchInterval := Duration.minutes 5 }
  let limitedOutcome ← match token with
    | none => pure (.error (.badDocument "fixture"))
    | some t => verifyIdToken limited provider discovery "the-nonce" t now
  let heldCount ← held.get

  pure
    [ ("oidc: an unknown kid is refused when no key answers it", rejected openOutcome)
    , ("oidc: and costs exactly one refetch, never more (AUTH-6.4)", eagerCount == 2)
    , ("oidc: a recent fetch means no refetch at all", heldCount == 1)
    , ("oidc: which is still a refusal rather than an acceptance", rejected limitedOutcome) ]
end Tests.Oidc
