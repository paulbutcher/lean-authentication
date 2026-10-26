# Running an OAuth 2.1 authorisation server

The other direction from [federated sign-in](federated-sign-in.md). There your application is the client of somebody else's provider; here it is the provider, issuing tokens to somebody else's client. It is written for MCP clients and implements the MCP authorization specification of 2026-07-28: `authorization_code` with PKCE `S256`, refresh tokens rotated on every use, and public clients only. It issues no ID tokens.

People sign in to it through the ordinary sign-in routes, so everything in [Getting started](getting-started.md) applies first.

## Wiring

```lean
def oauthPorts (db : SQLite) (peppers : PepperRing) : OAuth.Service.Ports IO :=
  { store := Sqlite.store db
    oauth := OAuth.sqlOAuthStore Sqlite.dialect (Sqlite.connection db)
    peppers }
```

```lean
def oauthConfig (tenant : TenantId) : OAuth.OAuthConfig tenant :=
  OAuth.OAuthConfig.standard ⟨"https://auth.example.com"⟩ [⟨"files:read"⟩, ⟨"files:write"⟩]
```

Scopes are your own strings; nothing here interprets one. The tables are separate from the sign-in tables and ship as their own pair of migrations, so a deployment without this server creates none of them.

A client identifies itself either by an `https` URL to a metadata document it hosts, or by registering at `/register`. Fetching documents needs `Ports.documents`, which is unset by default. The metadata document then advertises only dynamic registration, so no client is offered a mechanism that would be refused.

## Mounting

```lean
def oauth (ports : OAuth.Service.Ports IO) : OAuth.Http.Config :=
  { ports
    tenant := fun t => pure (some (config t))
    oauth := fun t => pure (some (oauthConfig t))
    defaultScopes := some [⟨"files:read"⟩] }
```

```lean
def app (http : Http.Config) (oauth : OAuth.Http.Config) : Routing.StatelessHandler .std :=
  let split := OAuth.Http.routes oauth
  Routing.toHandler (Http.routes http ++ split.browser ++ split.client)
```

| Path | Method |
| --- | --- |
| `/t/<tenant>/oauth/authorize` | `GET` the consent page, `POST` the answer |
| `/t/<tenant>/oauth/token` | `POST`, form encoded |
| `/t/<tenant>/oauth/register` | `POST`, RFC 7591 JSON |
| `/.well-known/oauth-authorization-server/t/<tenant>` | `GET` |

The routes come in two lists, and the split matters:

- **`browser`** is the consent page, answered by a person. If you use `Middleware.session` and `Middleware.antiForgery`, mount it inside them. If you do not, the form carries its own token derived from the session cookie.
- **`client`** is the token, registration and metadata endpoints, answered by a program carrying no cookie. Anti-forgery middleware refuses those by design, so mount them outside it.

Mount neither under a further prefix, because the metadata document advertises where they answer. Do not put the consent page behind a sign-in guard either: it sends people to sign in itself, at `Config.signIn`, whose default needs `/t/<tenant>/oauth/authorize` in the tenant's `returnToAllowlist`. A deployment serving a single tenant at its origin uses `OAuth.Http.Config (.origin tenant)` with `OAuthConfig.atOrigin`, so that clients discover it at the URL they try first. Nothing detects a mismatch between the two, and everything except discovery still works, so check it.

`defaultScopes` is what a request naming no scope is asked about. Unset, such a request is refused. `OAuthPages` replaces the consent page, but its field names belong to the library: `Scope.approvalField` and `ConsentForm.answerField`.

## Protecting a resource

```lean
def authorised {tenant : TenantId} (ports : OAuth.Service.Ports IO) (bearer : String) :
    IO (Except String (OAuth.Service.TokenClaims tenant)) := do
  match ← OAuth.Service.verify ports ⟨bearer⟩ ⟨"https://mcp.example.com/mcp"⟩ [⟨"files:write"⟩] with
  | .ok claims => pure (.ok claims)
  | .error rejection => pure (.error (OAuth.Service.challenge rejection))
```

A token is accepted only by the `resource` it was issued for. The challenge is the `WWW-Authenticate` value to answer with, naming every scope the operation needs. Where a hop might rewrite headers, as an AWS Lambda function URL rewrites that one, also serve `OAuth.Service.refusalDocument` as the body. A client that never sees the refusal retries for ever. `AccessToken.Rejection.name` says why a token was refused, for your logs.

## What a person has connected

```lean
def privacy {tenant : TenantId} (ports : OAuth.Service.Ports IO) (account : AccountId tenant) :
    IO Unit := do
  for connection in ← OAuth.Service.connections ports account do
    discard <| OAuth.Service.revoke ports account connection.client connection.resource
```

`connections` lists one row per client and resource still holding a live credential, which is exactly what `revoke` takes, so every row can have a button. A grant is also a [consent record](accounts.md#consent), and `OAuth.Service.grants` reads them.

## Housekeeping

```lean
def housekeeping (ports : OAuth.Service.Ports IO) (tenant : TenantId) : IO Unit := do
  discard <| OAuth.Service.pruneClients (tenant := tenant) ports (idle := Duration.days 30)
```

Some clients register afresh on every connection, so prune registrations nobody has used. Nothing rate limits these endpoints yet ([KNOWN_ISSUES.md](../KNOWN_ISSUES.md)); put a limiter in front of registration in particular.
