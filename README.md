# lean-authentication

Passwordless authentication for Lean 4 web applications: magic links with a cross-device
verification code, per-tenant signup policy, invitations, sessions, bounce handling, and consent
records.

The library says who someone is. It holds no roles or permissions and never decides who may call
an operation.

## Installing

```lean
require authentication from git
  "https://github.com/paulbutcher/lean-authentication" @ "v0.1.0"
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
| `AuthenticationHttp` | Ready-made sign-in routes |

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

`Clock` and `RandomBytes` are typeclasses. `import Authentication.Instances` supplies both, from
the host's wall clock and the operating system's random source. Nothing else in the package
imports that module, so a module meaning to pin the clock and forgetting gets a compile error
rather than the real one.

To keep the choice visible in your own code, `import Authentication.System` instead and write it
out:

```lean
instance : Clock IO := Clock.system
instance : RandomBytes IO := RandomBytes.system
```

Either way your own instance wins wherever it is in scope; the shipped ones are low priority. A
deployment whose nodes disagree about the time, or which draws entropy from an HSM, supplies its
own.

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
| `transport` | `Postmark.transport`, `Ses.transport` |
| `responsePolicy` | `SignInResponsePolicy.silent` (uniform silence) |
| `limiter` | `Sql.rateLimiter`, `RateLimiter.unlimited` |
| `responseFloor` | `ResponseFloor.sleeping ms`, `ResponseFloor.immediate` |
| `humanCheck` | `HumanCheck.unchecked`, or your bot-mitigation provider |
| `peppers` | The current pepper, plus any inside a rotation window |

`TenantConfig` also carries attempt and session lifetimes, the optional emailed code, the
`returnTo` allowlist, and the email templates, all with defaults. Peppers and provider tokens are
never defaulted.

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

`Ses.Subscription.topics` has no default, and an empty list accepts nothing: a valid signature
proves AWS sent the message, not that your topic did. Set your SNS topic to signature version 2;
version 1 is refused rather than verified with SHA-1.

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

## Housekeeping

```lean
Service.purgeExpired (tenant := t) ports (grace := Duration.days 1)  -- PurgeCounts
```

Removes attempts and sessions that stopped being usable more than `grace` ago. Nothing depends on
it having run, since all of it is refused on read anyway; what it bounds is table growth. **The
library does not schedule it.** Run it from whatever you already use for periodic work.

It sweeps nothing else. The audit log, consent records and delivery history are retention
questions rather than expiry ones, and the store offers no way to remove one of those. Rate
limiter counters need no sweeping: old buckets are dropped as new ones are opened.

## Schema

The SQL ships under `migrations/postgres` and `migrations/sqlite`, paired up and down and named in
`leanmigrate`'s convention. It is ordinary SQL, so any other means of applying it works.

Postgres objects live in an `auth` schema, SQLite objects behind an `auth_` prefix, both in your
own database, so `TransactionalStore` can enlist in your transaction.

**Applying them is yours, and nothing here checks that you did.** Upgrade without migrating and
the failure arrives when a statement first names a missing column.

`Sqlite.openInMemory` applies the schema; `Sqlite.openFile` and `Postgres.connect` do not.
`Sqlite.createSchemaSql` and `Postgres.createSchemaSql` are the whole schema as one string, and
`Postgres.createSchema` applies it.

Any other backend behind the `AuthStore` port has to pass
`Authentication.Store.Conformance.run`, which ships with the library.

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
- **`returnTo` is validated** against the tenant's allowlist before any redirect.
- **The audit log and the consent history are append only.** The port offers no update or delete.

`REQUIREMENTS.md` is the specification; `KNOWN_ISSUES.md` records where the implementation falls
short of it. Federated sign-in over OIDC, inbound email, passkeys and SAML are not implemented.

## Building

```
lake build
lake test
```

Tests are a subproject in `test/` with its own lakefile, so a project depending on this one is free
to name its own modules `Tests.*`. Warnings are errors.

`lake test` needs `libpq` and a Postgres server, because the reference backend has to pass the
conformance suite. It connects to `dbname=leanauthentication user=leanauthentication` unless
`AUTHENTICATION_POSTGRES` says otherwise, and reports an unreachable server as a failed check
rather than skipping.
