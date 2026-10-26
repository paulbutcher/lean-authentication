/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import AuthenticationHttp
import AuthenticationOidcHttp
import AuthenticationSqlite
import Authentication.Instances
import RoutingStd

/-! The code of `docs/federated-sign-in.md`, checked by `Tests.Docs`. -/

namespace Tests.Docs.Federated

open Authentication

private def sealedSecret : StoredSecret := .external "vault://acme/google"
private def sealedKey : StoredSecret := .external "vault://acme/apple"

def sealingRing (encoded : String) : Option Oidc.SealingRing :=
  (Leancrypto.Codec.Base64Url.decodeString encoded).map fun secret =>
    { current := { keyId := ⟨"sealing-2026-01"⟩, secret } }

def federation (secrets : Oidc.SealingRing) : IO (Oidc.SignInPorts IO) := do
  let http := Fetch.curlHttp
  let resolved := Oidc.clientSecrets (Oidc.secrets secrets)
  let tokens := Oidc.tokenEndpoint http
  pure
    { metadata := ← Oidc.metadata http
      identities := Oidc.identities http tokens resolved (← Oidc.keys http) }

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

def googleCredentials (text : Option String) : Option ProviderCredentials :=
  (text.bind StoredSecret.parse).map .clientSecret

def config (tenant : TenantId) : TenantConfig tenant :=
  { displayName := "Acme"
    baseUrl := ⟨"https://app.example.com"⟩
    sendingIdentity := { address := ⟨"no-reply", ⟨["example", "com"]⟩⟩, displayName := "Acme" }
    signupPolicy := .unrestricted
    providers }

def app (ports : Service.Ports IO) (oidc : Oidc.SignInPorts IO) : Routing.StatelessHandler .std :=
  let tenant := fun t => pure (some (config t))
  Routing.toHandler
    (Http.routes { ports, tenant } ++
      OidcHttp.routes
        { ports
          oidc
          tenant
          observeRefusal := fun t provider reason =>
            IO.eprintln s!"federated refused: {t.value} {provider.value} {reason.name}" })

end Tests.Docs.Federated
