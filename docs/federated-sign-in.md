# Signing in with Google, Apple, GitHub and others

People sign in with an account they already have at an identity provider, beside the magic link or, with [enforced SSO](enforce-sso.md), instead of it. Google, Apple and GitHub have each completed a sign-in against the live provider, and any OpenID Connect provider is configuration rather than code.

A provider's sign-in creates an account under the tenant's [signup policy](signup.md), exactly as a magic link does. It signs in an existing account in two cases: the identity is already linked to it, or the provider asserts a verified address that matches the account's. A provider that has not verified the address it asserts creates nothing and links nothing, and no configuration permits otherwise: linking on an unverified address is the classic account takeover.

Three targets, because verification links OpenSSL and the magic link routes must not: `AuthenticationFetch` makes the outbound requests, `AuthenticationOidc` speaks the protocol, and `AuthenticationOidcHttp` serves the routes.

## Wiring

```lean
def federation (secrets : Oidc.SealingRing) : IO (Oidc.SignInPorts IO) := do
  let http := Fetch.curlHttp
  let resolved := Oidc.clientSecrets (Oidc.secrets secrets)
  let tokens := Oidc.tokenEndpoint http
  pure
    { metadata := ← Oidc.metadata http
      identities := Oidc.identities http tokens resolved (← Oidc.keys http) }
```

`metadata` and `keys` each hold a cache, of the discovery document and the key set, kept as long as the provider's response allows. Build them once at startup; built per request, every sign-in becomes a request to the provider.

## Providers

Providers belong to the tenant, in `TenantConfig.providers`:

```lean
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
```

Apple mints its client secret per request from a signing key, and answers with a cross-site `POST`, which is what `formPost` is for: it makes the state cookie `SameSite=None`, without which every Apple sign-in would arrive with no cookie and be refused. GitHub is not OpenID Connect, so its endpoints are configured rather than discovered.

## Other providers

Any provider that publishes a discovery document takes the path Google does: Okta, Auth0, Keycloak, Cognito, Zitadel, Twitch and LinkedIn among them. Two things decide whether one works first time.

- **The issuer is what everything is checked against.** A provider whose issuer names a tenant, realm or pool needs one entry per tenant, realm or pool. Microsoft's `common` and `organizations` endpoints match no single issuer, and are refused.
- **A first sign-in needs `email_verified`.** A provider that omits it, as Microsoft Entra ID does, is refused as `address-not-verified` on the sign-in that would create or link an account. An identity already linked signs in regardless.

A provider that is neither OpenID Connect nor GitHub needs a `ProviderIdentities` of your own, the seam `Oidc.identities` chooses between.

## Secrets

A provider's secret is never configured in the clear; `auth-seal` seals it. Mint a sealing key, and keep it with the deployment's other secrets, never in the database it protects:

```sh
$ lake exe auth-seal key
0NKWg0-wFDSSobc8JGKt3PadxinGuX5lHgMThxnlMvk
```

```lean
def sealingRing (encoded : String) : Option Oidc.SealingRing :=
  (Leancrypto.Codec.Base64Url.decodeString encoded).map fun secret =>
    { current := { keyId := ⟨"sealing-2026-01"⟩, secret } }
```

Seal each secret. It is read from standard input, so it never appears in the process list or a shell history, and the tenant, provider and field are bound into the result:

```sh
$ export AUTH_SEALING_KEY=0NKWg0-wFDSSobc8JGKt3PadxinGuX5lHgMThxnlMvk
$ lake exe auth-seal seal acme google client-secret sealing-2026-01 < google-client-secret.txt
v1.s.c2VhbGluZy0yMDI2LTAx.oENlJX5Lt9ok-GY9.g8kiJeRjFpqnVg.dc9zy6lwzRgzucgNZqyoCA
```

That text is what your configuration holds, and `StoredSecret.parse` reads it back, refusing rather than panicking on a value that is missing or mistyped:

```lean
def googleCredentials (text : Option String) : Option ProviderCredentials :=
  (text.bind StoredSecret.parse).map .clientSecret
```

Apple's `.p8` is sealed the same way, as the file's bytes, under `signing-key`. A secret sealed against the wrong tenant, provider or field configures cleanly and refuses every sign-in, so check what a value opens under. The check never prints the secret, so it is safe to run against a live deployment:

```sh
$ lake exe auth-seal check acme google client-secret sealing-2026-01 <<< "$GOOGLE_CLIENT_SECRET"
opens, sealed under key id sealing-2026-01, key id held sealing-2026-01
```

To rotate, mint a second key, keep the old one in `SealingRing.retired`, and reseal each secret under the new key identifier; a check says whether a value still carries the old one. Secrets held in KMS or Vault are configured as `.external "some/reference"` and resolved by a `Secrets` port of your own.

## Mounting

```lean
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
```

| Path | Method |
| --- | --- |
| `/t/<tenant>/federated/<provider>` | `GET`, sends the browser to the provider |
| `/t/<tenant>/federated/<provider>` | `POST`, adds the provider to the account signed in |
| `/t/<tenant>/federated/<provider>/callback` | `GET` or `POST`, the provider's answer |
| `/t/<tenant>/federated/<provider>/recover` | `POST`, adds the provider under a [recovery grant](recovery.md) |

A sign-in button is a link to the `GET` start, which also takes `returnTo`. Register the redirect URI with each provider exactly as `OidcHttp.callbackUri` builds it from the tenant's base URL, since providers compare it as a string. Federated sign-in adds migrations of its own, which are yours to apply as all of them are.

## Adding a provider to an account

Post a form to the start from a page where the person is signed in, and the provider is added to their account rather than signed in as:

```html
<form method="post" action="/t/acme/federated/apple">
  <button>Add Apple</button>
</form>
```

The account is read from the session cookie, never from the request, and a `POST` from another site carries no `SameSite=Lax` cookie, so a forged form starts nothing. The address the provider asserts plays no part, which makes this the only way to reach an account through **Apple's Hide My Email**: a relay address matches no account and never will.

`Service.linkedIdentities` lists what an account has linked, and `Service.unlinkIdentity` removes one, refusing to leave the account no way in. On a tenant that admits the magic link, the primary address counts as a way in.
