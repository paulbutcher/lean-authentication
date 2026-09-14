/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import AuthenticationOidcHttp
import AuthenticationSqlite
import Authentication.Instances

/-!
The federated sign-in wiring the README prints.

It is here so that it compiles. A worked example that has drifted from the library is worse than
none, because it is read as the thing that works and a reader who copies it learns that it does
not. Nothing is run: compiling is the whole of the check.
-/

namespace Tests.ReadmeWiring
open Authentication

private def sealedSecret : StoredSecret := .external "vault://acme/google"
private def sealedKey : StoredSecret := .external "vault://acme/apple"

/-- The wiring under "Federated sign-in / Wiring". -/
def federation (secrets : Oidc.SealingRing) : IO (Oidc.SignInPorts IO) := do
  let http := Fetch.curlHttp
  let resolved := Oidc.clientSecrets (Oidc.secrets secrets)
  let tokens := Oidc.tokenEndpoint http
  pure
    { metadata := ← Oidc.metadata http
      identities := Oidc.identities http tokens resolved (← Oidc.keys http) }

/-- The three under "Providers". -/
def providers : List ProviderConfig :=
  [ { id := ⟨"google"⟩
      issuer := "https://accounts.google.com"
      clientId := "1234.apps.googleusercontent.com"
      credentials := .clientSecret sealedSecret }
  , { id := ⟨"apple"⟩
      issuer := "https://appleid.apple.com"
      clientId := "com.example.service"
      credentials := .signingKey "TEAM123456" "KEY7890AB" sealedKey
      formPost := true
      scopes := ["openid", "email", "name"] }
  , { id := ⟨"github"⟩
      issuer := "https://github.com"
      clientId := "Iv1.0123456789abcdef"
      credentials := .clientSecret sealedSecret
      endpoints := .configured
        "https://github.com/login/oauth/authorize"
        "https://github.com/login/oauth/access_token"
        "https://api.github.com/user"
        "https://api.github.com/user/emails"
      scopes := ["read:user", "user:email"] } ]

/-- The call under "Secrets". -/
def sealOne (sealingKey : ByteArray) : IO (Except SecretError SealedSecret) :=
  Oidc.sealSecret
    { keyId := ⟨"sealing-2026-01"⟩, secret := sealingKey }
    { tenant := ⟨"acme"⟩, provider := ⟨"google"⟩, field := .clientSecret }
    "the-secret-google-gave-you".toUTF8

private def config (tenant : TenantId) : TenantConfig tenant :=
  { displayName := "Acme"
    baseUrl := ⟨"https://app.example.com"⟩
    sendingIdentity := { address := ⟨"no-reply", ⟨["example", "com"]⟩⟩, displayName := "Acme" }
    signupPolicy := .unrestricted
    providers }

/-- The mount under "Mounting". -/
def federatedRoutes (ports : Service.Ports IO) (oidc : Oidc.SignInPorts IO) :
    Std.Http.Server.StatelessHandler :=
  OidcHttp.handler
    { ports
      oidc
      tenant := fun t => pure (some (config t)) }

end Tests.ReadmeWiring
