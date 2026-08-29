# lean-authentication

- Passwordless authentication for Lean 4 web applications: magic links with a cross-device
verification code, per-tenant signup policy, invitations, sessions, bounce handling, and consent
records.
- An OAuth 2.1 authorisation server.

The library says who someone is. It holds no roles or permissions and never decides who may call
an operation.

## Installing

```toml
[[require]]
name = "authentication"
git = "https://github.com/paulbutcher/lean-authentication"
```

Each target is a separate `lean_lib`. Depend only on what you use.

| Target | Contents |
| --- | --- |
| `Authentication` | Domain model, sign-in state machine, service, storage port |
| `AuthenticationSql` | Store and rate limiter for any SQL backend |
| `AuthenticationSqlite` | SQLite backend |
| `AuthenticationPostgres` | Postgres backend (needs `libpq`) |
| `AuthenticationPostmark` | Postmark transport and webhook endpoint |
| `AuthenticationSes` | Amazon SES transport and SNS callback endpoint |
| `AuthenticationHttp` | Ready-made sign-in routes, and the authorisation server's own endpoints |
| `AuthenticationOAuth` | OAuth 2.1 authorisation server, for MCP clients and anything else |

## The flow

1. Someone enters their address. `Service.begin` mints an attempt, sends the mail, and returns a
   cookie to set.
2. They open the link. `Service.openLink` reports which case it is:
   - **Same browser**: a confirm page, then `Service.confirmSignIn` issues the session.
   - **Different device**: a code is displayed, typed into the original browser, and
     `Service.submitCode` issues the session.
3. `Service.identify` turns the session cookie's credential into an `AccountId`.

An account is created by the first sign-in that succeeds, subject to the tenant's signup policy.
There is no registration call.

Each step returns an `Outcome`: the views to render, cookies to set and clear, the session
credential if one was issued, and the account if one was created.

## Wiring

`Clock` and `RandomBytes` are typeclasses, and no instance is in scope until you ask for one.
`import Authentication.Instances` supplies both, from the host's wall clock and the operating
system's random source. To keep them visible in your own code instead:

```lean
import Authentication.System

instance : Clock IO := Clock.system
instance : RandomBytes IO := RandomBytes.system
```

The shipped instances are low priority, so your own wins wherever it is in scope.

```lean
open Authentication

def ports (db : SQLite) (secret : ByteArray) (postmarkToken : String) : Service.Ports IO :=
  { store := Sqlite.store db
    transport := Postmark.transport { serverToken := postmarkToken }
    responsePolicy := SignInResponsePolicy.silent IO
    limiter := Sql.rateLimiter Sqlite.dialect (Sqlite.connection db)
    responseFloor := ResponseFloor.sleeping 400
    humanCheck := HumanCheck.unchecked IO
    peppers := { current := { keyId := ⟨"2026-01"⟩, secret } } }

def config (tenant : TenantId) : TenantConfig tenant :=
  { displayName := "Acme"
    baseUrl := ⟨"https://app.example.com"⟩
    sendingIdentity := { address := ⟨"no-reply", ⟨["example", "com"]⟩⟩, displayName := "Acme" }
    signupPolicy := .domainAllowlist [⟨["example", "com"]⟩] (includeSubdomains := true)
    returnToAllowlist := ["/dashboard"] }
```

| Port | Implementations |
| --- | --- |
| `store` | `Sqlite.store`, `Postgres.store` |
| `transport` | `Postmark.transport`, `Ses.transport`, `EmailTransport.capturing` |
| `responsePolicy` | `SignInResponsePolicy.silent` (uniform silence) |
| `limiter` | `Sql.rateLimiter`, `RateLimiter.unlimited` |
| `responseFloor` | `ResponseFloor.sleeping ms`, `ResponseFloor.immediate` |
| `humanCheck` | `HumanCheck.unchecked`, or your bot-mitigation provider |
| `peppers` | The current pepper, plus any inside a rotation window |

`TenantConfig` also carries attempt and session lifetimes, the optional emailed code, the
`returnTo` allowlist, the session cookie's path, and the email templates, all with defaults.
Peppers and provider tokens are never defaulted.

Both providers need an account and credentials, which a developer running the application locally
has not got, and the magic link exists nowhere but inside the message. `EmailTransport.capturing`
takes a sink of your own instead of sending, and `EmailTransport.console` is that sink wired to
standard output:

```lean
-- prints the message
transport := EmailTransport.console

-- or hands it to a sink of your own, which is what a test wants
transport := EmailTransport.capturing fun mail => sent.modify (· ++ [mail])
```

Either reports success, with the id a real transport would have returned for the same message.
Development only: the message carries the sign-in credential in the clear, so anyone who can read
the console, or whatever the sink writes to, can sign in as whoever asked to.

## Mounting the routes

```lean
def routes (db : SQLite) (secret : ByteArray) (token : String) :
    Std.Http.Server.StatelessHandler :=
  Http.handler
    { ports := ports db secret token
      tenant := fun t => pure (some (config t)) }
```

| Path | Method |
| --- | --- |
| `/t/<tenant>/signin` | `GET` form, `POST` to send the mail |
| `/t/<tenant>/signin/link` | `GET`, the magic link target |
| `/t/<tenant>/signin/confirm` | `POST`, same-device completion |
| `/t/<tenant>/signin/code` | `POST`, cross-device code entry |
| `/t/<tenant>/signin/emailed-code` | `POST`, the optional code from the mail body |
| `/t/<tenant>/invitation/accept` | `GET`, the invitation link target |
| `/t/<tenant>/webhooks/<name>` | `POST`, provider callbacks |

`Http.routes` returns the same list for mounting into a router you already have.

`Config.pages` replaces the rendering; the defaults are unstyled and semantic. The emailed-code
form appears only where `TenantConfig.emailedCodeEnabled` is set. Nothing administrative is
served: invitations, revocation and suppression have no route.

Two things remain yours:

- The per-IP rate limit reads the source address from `Middleware.ForwardedFor` and nowhere else.
  Install `Middleware.forwardedRemoteAddr` with a header you trust.
- Bot mitigation is the `HumanCheck` port, whose default admits everyone. Set `humanProofField`
  to your provider's form field name and give `Ports.humanCheck` an implementation.

Routing it yourself is supported; the response guarantees below then become yours to reproduce.

## Sessions

```lean
Service.identify ports config credential          -- Option (SessionIdentity tenant)
Service.sessions ports account (presented := ...) -- List (SessionSummary tenant)
Service.revokeSession ports account session       -- Bool
Service.revokeAllSessions ports account reason
Service.changePrimaryEmail ports account address
Service.deactivateAccount ports account
Service.reactivateAccount ports account
```

Sessions are server-side and revocable. The idle timeout slides on use, capped by an absolute
lifetime. Changing the primary address and deactivating each revoke every session in the same
call, and a deactivated account cannot sign in until reactivated.

The session cookie is issued with `TenantConfig.sessionCookiePath`, which defaults to
`/t/<tenant>`. Set the field to a path that covers your application if different.

## Invitations

```lean
Service.createInvitation ports config address metadata
Service.resendInvitation ports config id
Service.revokeInvitation ports id
Service.invitations ports  -- each with pending / accepted / expired / revoked standing
```

An invitation grants one address in one tenant. `metadata` is an opaque payload stored verbatim
and handed back on acceptance, which is where your own roles go. Acceptance runs the full sign-in
flow, cross-device code included. Invitations are single use, revocable, and last 7 days by
default; resending rotates the token and invalidates the old link.

## Bounces and suppression

Give each transport's endpoint to `Http.Config.webhooks`:

```lean
webhooks :=
  [ Postmark.endpoint { username := "hook", password := hookPassword },
    Ses.endpoint (Ses.curlSubscription [bouncesTopicArn]) ]
```

A hard bounce or spam complaint suppresses the address; a transient failure is counted. Suppressed
addresses are refused before the transport is asked.

`Ses.Subscription.topics` has no default and an empty list accepts nothing, so name every topic
you expect. Set those topics to signature version 2; version 1 is refused.

To receive callbacks some other way, `Postmark.deliveryEvents` and `Ses.deliveryEvents` parse a
payload and `Service.ingestDelivery` records one. Verification is then yours.

```lean
Service.suppressed ports address        -- Bool
Service.suppressAddress ports address
Service.clearSuppression ports address
Service.deliveryReport ports            -- addresses failing often enough to report
```

## Consent records

The library stores consent and never captures it: ask somebody who is already signed in, and
record what they said.

```lean
Service.grantConsent ports account ⟨"marketing"⟩ "2026-01"
Service.withdrawConsent ports account ⟨"marketing"⟩ "2026-01"
Service.consents ports account         -- where each subject stands now
Service.consentHistory ports account   -- every entry, oldest first
Service.consenting ports ⟨"marketing"⟩ -- the accounts to write to
```

Subject and version are your own strings, stored verbatim and never interpreted. The history is
append only: withdrawing adds an entry rather than editing one.

## Authorisation server

`AuthenticationOAuth` is the other direction from signing in with somebody else's provider: it is
the provider that somebody else's client gets tokens from. It implements the MCP authorization
specification of 2026-07-28 and the OAuth 2.1 subset that one selects, which is
`authorization_code` with PKCE `S256`, refresh tokens rotated on every use, and public clients
only.

```lean
open Authentication.OAuth

def oauthPorts : Service.Ports IO :=
  { store := Sqlite.store db                                  -- sessions, consent, audit
    oauth := sqlOAuthStore Sqlite.dialect (Sqlite.connection db)
    documents := some yourFetcher                             -- one HTTPS GET, or none
    peppers }

def oauthConfig : OAuthConfig tenant :=
  OAuthConfig.standard ⟨"https://auth.example.com"⟩ [⟨"files:read"⟩, ⟨"files:write"⟩]
```

`metadataDocument oauthPorts.documents oauthConfig` is the RFC 8414 document. The fetcher it is
handed is what `client_id_metadata_document_supported` reports, so a deployment with no fetcher
advertises no mechanism it would then refuse, and a client registers dynamically instead.

`AuthenticationOAuth` decides and renders nothing. These four are the whole of it:

```lean
Service.authorize ports config params sessionCookie   -- Outcome: consent, respond, authenticate, refuse
Service.conclude  ports config decision               -- what the person said
Service.token     ports config params                 -- Except ErrorResponse TokenResponse
Service.register  ports body                          -- RFC 7591, application/json
```

`authorize` never renders anything. It answers with one of four outcomes: `consent` carries
everything a consent page must show, including the hosts of the `client_id` and the redirect URI;
`respond` is a redirect the user agent should follow, success or error; `authenticate` means you
should run the sign-in flow and ask again; `refuse` means the client could not be established and
nothing may be sent to it. A grant is recorded as a consent record, so revoking one is
`Service.revoke` and it shows up in `Service.grants` beside everything else the person agreed to.

`Params.ofQuery`, which lives in `AuthenticationHttp` because it is the one place this server names a transport, turns a query or a form body into those parameters. It keeps duplicates, which is what lets a parameter sent twice be refused as OAuth 2.1 §4.1.1 requires, and it decodes names and values once, so that nothing downstream compares a percent-encoded form against a decoded one.

A privacy page also needs to say what is connected now, which the history cannot answer: it
records decisions rather than what is live. `Service.connections` answers from the credentials:

```lean
Service.connections ports account   -- client, name, origin, resource, scopes, since, lastUsedAt
```

One row per client and resource that still holds a credential which has neither expired nor been
revoked, which is exactly what `Service.revoke` takes, so every row maps onto a button. Nothing
is fetched: a metadata document client's name is whatever the cache holds. `Consent.parts` reads
a subject from `Service.grants` back as the client and resource it names.

A client identifier is either an `https` URL that resolves to a metadata document the client
hosts, or one this server issued at `/register`. Both reach the same flow. Documents are cached
for as long as the response's cache headers allow, and registrations that nobody has used can be
pruned:

```lean
Service.pruneClients ports (idle := Duration.days 30)
```

For a resource server, `Service.verify` is the whole of token validation:

```lean
Service.verify ports presented ⟨"https://mcp.example.com/mcp"⟩ [⟨"files:write"⟩]
```

The audience is checked against the `resource` the token was issued for and nothing else, and an
operation that needs more scope comes back as `insufficientScope`, which `Service.challenge`
turns into the `WWW-Authenticate` value naming what to ask for.

`Service.refusalDocument` is the same refusal as a JSON body. Serve it alongside the header wherever a hop might rewrite headers on the way out: an AWS Lambda function URL renames `WWW-Authenticate`, and a client that never sees the refusal, or the `resource_metadata` in it, reconnects forever against a grant it cannot learn is wrong.

## Mounting the authorisation server

`AuthenticationHttp` serves the four endpoints, for the reason the sign-in routes are there:
what an application gets wrong about OAuth is almost never the protocol, it is the transport
around it. Calling the four functions above yourself remains supported and is what a deployment
whose framework owns the request does.

```lean
def oauth : OAuth.Http.Config :=
  { ports := oauthPorts
    tenant := fun t => pure (some (config t))   -- the sign-in routes' own lookup
    oauth := fun t => pure (some (oauthConfig t))
    defaultScopes := some [⟨"files:read"⟩] }    -- unset refuses a request naming no scope
```

| Path | Method |
| --- | --- |
| `/t/<tenant>/oauth/authorize` | `GET` the consent page, `POST` the answer |
| `/t/<tenant>/oauth/token` | `POST`, form encoded |
| `/t/<tenant>/oauth/register` | `POST`, RFC 7591 JSON |
| `/.well-known/oauth-authorization-server/t/<tenant>` | `GET` |

`Config.mountedAt` chooses between those paths and the same four at the origin, which is what a
deployment serving one tenant wants: RFC 8414 §3 puts the well-known suffix *ahead* of an issuer's
path, so an issuer with a path is discovered only at a URL a client constructs, while an issuer
with none is discovered at the URL every client tries. `OAuthConfig.standard` pairs with
`.perTenant` and `OAuthConfig.atOrigin` with `.origin`; nothing detects a mismatch at run time,
because everything works except discovery.

`OAuth.Http.routes` returns the routes in two lists rather than one, and the split is the point:

- **`browser`** is `/oauth/authorize`, answered by a person. Its `POST` must be unpostable from
  another site, so mount it inside `Middleware.session` and `Middleware.antiForgery` if you have
  them. If you do not, the consent form carries a token derived from the session cookie under the
  current pepper and the route checks it, exactly as the sign-in routes do with theirs.
- **`client`** is the token, registration and metadata endpoints, answered by a program carrying
  no cookie. Anti-forgery middleware refuses those by design, so they must be mounted outside it.

`OAuth.Http.handler config wrap` mounts both, applying `wrap` to the browser half alone. Neither
list may be mounted under a further prefix: the metadata document advertises where they answer.

`OAuthPages` replaces the rendering, with `consent` and `refusedClient` and unstyled defaults. The
form's field names are the library's, not the page's: `Scope.approvalField` names the checkbox a
scope carries, encoded so that whatever the client put in the scope the field name is still one a
browser sends back, and `ConsentForm.answerField` carries the answer itself. `Scope.approved` and
`ConsentForm.approved` read them back, so the two encodings cannot disagree.

`Config.defaultScopes` is what a request naming no `scope` at all is asked about. OAuth 2.1
§3.2.2.1 allows a default set or a refusal; unset is the refusal, and it is unset rather than
quietly `scopesSupported` because those are two different statements. The page asks either way,
and a box left unticked is a scope withheld.

`authorize` is not behind a sign-in guard, and must not be put behind one: whether a request with
no session should sign somebody in, refuse, or redirect an error to the client is the
authorisation server's answer, and `prompt=none` is the case where a sign-in page is the wrong
one. `Config.signIn` says where the requests that do need somebody signed in are sent, and its
default needs the authorization endpoint's path in the tenant's `returnToAllowlist`.

Every response carries `Cache-Control: no-store`, the query and the form body are read apart and
never merged, and the `POST` to `/oauth/authorize` re-reads the request rather than reassembling
it from hidden fields.

## Housekeeping

```lean
Service.purgeExpired (tenant := t) ports (grace := Duration.days 1)  -- PurgeCounts
```

Removes attempts and sessions that stopped being usable more than `grace` ago, and bounds table
growth. Correctness does not depend on it. **The library does not schedule it**: run it from
whatever you already use for periodic work.

Nothing else is swept. The audit log, consent records and delivery history are never removed, and
rate limiter counters drop their own stale buckets.

## Schema

The SQL ships under `migrations/postgres` and `migrations/sqlite`, paired up and down and named in
`leanmigrate`'s convention. It is ordinary SQL, so any other means of applying it works.

Postgres objects live in an `auth` schema, SQLite objects behind an `auth_` prefix, both in your
own database, so `TransactionalStore` can enlist in your transaction.

**Applying them is yours, and nothing here checks that you did.**

`Sqlite.openInMemory` applies the schema; `Sqlite.openFile` and `Postgres.connect` do not.
`Sqlite.createSchemaSql` and `Postgres.createSchemaSql` are the whole schema as one string, and
`Postgres.createSchema` applies it.

The authorisation server's tables are separate, so a deployment that does not use it creates
none of them. They ship as another pair of migrations, and `OAuth.sqliteSchemaSql` and
`OAuth.postgresSchemaSql` are the same SQL as a string.

Any other backend behind the `AuthStore` port has to pass
`Authentication.Store.Conformance.run`, which ships with the library.

A client that already owns a connection pool can implement `Sql.SqlConnection` over it rather
than run a second connection alongside it. `Handle` is whatever the pool lends out, statements
outside a transaction may each borrow their own, and `runTransaction` is handed the one its
`BEGIN` ran on and passes it to the block, so a transaction cannot spread itself over connections
chosen independently. `Sql.sqlAuthStore` and `Sql.sqlTransactionalStore` turn one into the ports.

## Sending domain DNS

The `From` domain needs all of these before mail is delivered rather than filed:

- **SPF** authorising the provider's servers.
- **DKIM** with the provider's selector.
- **DMARC** on the organisational domain, tested at `p=none` first.
- **MX** on the sending subdomain: a real one, or an explicit null MX (`0 .`, RFC 7505). Absence
  is scored against you.

## Guarantees

- **Tenant isolation is typed.** Identifiers carry their tenant (`AccountId tenant`), so an
  expression crossing tenants does not compile.
- **No credential is stored.** Magic tokens, codes, session identifiers and invitation tokens are
  held as HMAC digests under a server-side pepper. Rotation has an overlap window.
- **One attempt is live per address**, and starting a second abandons the first atomically. Magic
  tokens are single use; code entry is capped at five tries.
- **A link opened on another device signs nobody in on that device.** Completion always requires
  the browser holding the attempt cookie.
- **Sign-in responses say nothing by default.** Every outcome maps to the same message, and the
  shipped routes give every outcome the same status, headers and one `Set-Cookie`, including
  outcomes that began no attempt. `ResponseFloor` normalises the latency.
- **Rate limiting counts five scopes**: per (tenant, address), per address across all tenants, per
  source IP, per tenant, and globally.
- **Provider callbacks are verified inside the endpoint**, before the payload is read. The SNS
  certificate is fetched only from a recognised host, decided before the fetch, and the topic is
  checked.
- **`returnTo` is validated** against the tenant's allowlist before any redirect. It travels as a
  URI reference in its encoded form: a caller with a target whose own query holds encoded values
  encodes the whole reference once for the form field, and what reaches the browser is that
  reference, escaped only where a header value could not otherwise hold it.
- **The audit log and the consent history are append only.** The port offers no update or delete.
- **An authorization code is redeemed at most once**, a refresh token rotated at most once, and
  either presented twice revokes everything its grant issued. Both are theorems about the state
  and compare-and-set in the store.
- **A token's audience is the `resource` its request named**, and its scopes are a subset of what
  was consented to. Both are theorems, and verification refuses a token presented anywhere else.
- **A redirect URI is compared as a string**, with the port ignored for loopback URIs and for
  nothing else. That the exception admits no other host is a theorem.

`REQUIREMENTS.md` is the specification; `KNOWN_ISSUES.md` records where the implementation falls
short of it. Federated sign-in over OIDC, inbound email, passkeys and SAML are not implemented, and the authorisation server issues no ID tokens.

## Building

```
lake build
lake test
```

Tests are a subproject in `test/` with its own lakefile, so a project depending on this one is free
to name its own modules `Tests.*`. Warnings are errors.

`lake test` needs `libpq` and a Postgres server. It connects to
`dbname=leanauthentication user=leanauthentication` unless `AUTHENTICATION_POSTGRES` says
otherwise, and reports an unreachable server as a failed check rather than skipping.
