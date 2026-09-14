/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import AuthenticationOidc
import Authentication.Instances

/-!
A provider that is not OpenID Connect (AUTH-6.9).

There is no ID token here, which is the point: the same port answers, and the flow above it cannot
tell which kind of provider it was talking to. What these check is the part that has no signature
behind it, and so has to be got right by reading: which address is chosen, and whether an
unverified one can ever be.
-/

namespace Tests.OAuth2Provider
open Authentication Authentication.Oidc

private def now : Timestamp := ⟨1780000000⟩

private def provider : ProviderConfig :=
  { id := ⟨"github"⟩
    issuer := "https://github.test"
    clientId := "client-abc"
    credentials := .clientSecret (.external "unused")
    endpoints := .configured "https://github.test/login/oauth/authorize"
      "https://github.test/login/oauth/access_token"
      "https://api.github.test/user" "https://api.github.test/user/emails"
    scopes := ["read:user", "user:email"] }

private def discovery : Discovery :=
  { issuer := provider.issuer
    authorizationEndpoint := "https://github.test/login/oauth/authorize"
    tokenEndpoint := "https://github.test/login/oauth/access_token"
    jwksUri := "" }

private def secrets : ClientSecrets IO := { produce := fun _ _ _ _ => pure (.ok "a-secret") }
private def tokens : TokenEndpoint IO :=
  { exchange := fun _ _ _ _ _ _ => pure (.ok "an-access-token") }

/-- Answers the profile call and the address call from a script, and records the headers each
request carried so a check can say the token actually travelled. -/
private def scripted (profile emails : String) (seen : IO.Ref (List (String × String))) :
    Fetch.Http IO where
  send request := do
    let auth := (request.headers.find? (·.1 == "Authorization")).map (·.2) |>.getD ""
    seen.modify (· ++ [(request.url, auth)])
    let body := if (request.url.splitOn "emails").length > 1 then emails else profile
    pure (.ok { status := 200, headers := [], body := body.toUTF8 })

private def redeemWith (profile emails : String) :
    IO (Except OidcError ProviderAnswer × List (String × String)) := do
  let seen ← IO.mkRef []
  let port := oauth2Identities (scripted profile emails seen) tokens secrets
  let answer ← port.redeem ⟨"acme"⟩ provider discovery "code" "https://back" "verifier" "" now
  pure (answer, ← seen.get)

private def onlyPrimaryVerified : String :=
  "[{\"email\":\"old@example.com\",\"primary\":false,\"verified\":true},
    {\"email\":\"person@example.com\",\"primary\":true,\"verified\":true}]"

private def primaryUnverified : String :=
  "[{\"email\":\"fallback@example.com\",\"primary\":false,\"verified\":true},
    {\"email\":\"claimed@example.com\",\"primary\":true,\"verified\":false}]"

private def noneVerified : String :=
  "[{\"email\":\"claimed@example.com\",\"primary\":true,\"verified\":false}]"

def checks : IO (List (String × Bool)) := do
  let (good, calls) ← redeemWith "{\"id\":4242,\"login\":\"octo\"}" onlyPrimaryVerified
  let (fallback, _) ← redeemWith "{\"id\":4242}" primaryUnverified
  let (refused, _) ← redeemWith "{\"id\":4242}" noneVerified
  let (anonymous, _) ← redeemWith "{\"login\":\"octo\"}" onlyPrimaryVerified
  let rejected {α : Type} : Except OidcError α → Bool
    | .error _ => true
    | .ok _ => false
  pure
    [ ("oauth2: the identity is keyed on the provider's number, not the login (AUTH-6.6)",
        (good.toOption.map (·.identity.subject)) == some "4242")
    , ("oauth2: and on the issuer the tenant configured",
        (good.toOption.map (·.identity.issuer)) == some "https://github.test")
    , ("oauth2: the verified primary address is the one chosen",
        (good.toOption.bind (·.address.map (·.render))) == some "person@example.com")
    , ("oauth2: an address only reaches the linking rule marked verified (AUTH-6.7)",
        (good.toOption.map (·.addressVerified)) == some true)
    , ("oauth2: an unverified primary is passed over for a verified one",
        (fallback.toOption.bind (·.address.map (·.render))) == some "fallback@example.com")
    , ("oauth2: an account with no verified address signs in nobody", rejected refused)
    , ("oauth2: a profile with no id is refused rather than keyed on the login", rejected anonymous)
    , ("oauth2: two calls were made, profile then addresses", calls.length == 2)
    , ("oauth2: both carried the access token",
        calls.all (·.2 == "Bearer an-access-token"))
    , ("oauth2: and went to the configured endpoints",
        (calls.map (·.1)) == ["https://api.github.test/user", "https://api.github.test/user/emails"]) ]

/-- A provider configured as discovering is refused here rather than guessed at, and one
configured with endpoints needs no document fetched for it. -/
def endpointChecks : IO (List (String × Bool)) := do
  let seen ← IO.mkRef []
  let misconfigured := { provider with endpoints := .discovered }
  let port := oauth2Identities (scripted "{}" "[]" seen) tokens secrets
  let answer ← port.redeem ⟨"acme"⟩ misconfigured discovery "code" "https://back" "v" "" now
  let calls ← seen.get
  let never : Fetch.Http IO := { send := fun _ => pure (.error (Leancurl.CurlError.ofCode 7)) }
  let found ← (← metadata never).discover provider
  pure
    [ ("oauth2: a provider with no configured endpoints is refused",
        match answer with | .error _ => true | .ok _ => false)
    , ("oauth2: and nothing was fetched on its behalf", calls.isEmpty)
    , ("oauth2: configured endpoints need no discovery document (AUTH-6.9)",
        (found.toOption.map (·.tokenEndpoint))
          == some "https://github.test/login/oauth/access_token") ]

end Tests.OAuth2Provider
