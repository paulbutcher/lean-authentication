# Running in production

[Getting started](getting-started.md) used three development stand-ins: an in-memory database, a console transport, and a pepper drawn at startup. This guide replaces each, and covers what a deployment has to do that the library deliberately does not.

```lean
import AuthenticationHttp
import AuthenticationPostgres
import AuthenticationPostmark
import AuthenticationSes
import Authentication.Instances
import RoutingStd
```

## The ports

```lean
def ports (db : Postgres.Connection) (peppers : PepperRing) (postmarkToken : String) :
    Service.Ports IO :=
  { store := Postgres.store db
    transport := Postmark.transport { serverToken := postmarkToken }
    responsePolicy := SignInResponsePolicy.silent IO
    limiter := Sql.rateLimiter Postgres.dialect (Postgres.connection db)
    responseFloor := ResponseFloor.sleeping 400
    humanCheck := HumanCheck.unchecked IO
    peppers }
```

`ResponseFloor.sleeping 400` holds every sign-in response to at least 400 milliseconds, so that sending mail and not sending it take the same time. Set it above your transport's slowest ordinary send.

## The database

`Postgres.connect` takes a libpq connection string. Its objects live in an `auth` schema inside your own database. A client that already owns a connection pool can implement `Sql.SqlConnection` over it, and `Sql.sqlAuthStore` turns that into the store. A backend of your own behind the `AuthStore` port must pass `Authentication.Store.Conformance.run`, which ships with the library.

**Applying the migrations is yours, and nothing checks that you did.** They ship as SQL under `migrations/postgres` and `migrations/sqlite`, paired up and down and named in `leanmigrate`'s convention, so any migration tool can apply them. A database missing a migration fails when a statement first names the missing column, not at startup. `Sqlite.openInMemory` applies the schema itself; `Sqlite.openFile` and `Postgres.connect` do not. `Postgres.createSchema` applies the whole schema at once, and every Postgres statement in it is idempotent.

SQLite (`Sqlite.openFile`, which turns on WAL) suits a single process only, because every instance must be able to serve every request and a SQLite file is not shared between hosts. It has one writer, so the rate limiter's counters contend with every other write; `limiter` can point at a different database from `store`.

To create your own records in the same transaction as an account, drive the flow yourself through `Postgres.transactionalStore`. That needs the library's tables in your database, which is the price of atomic provisioning.

## Peppers

Every stored credential is a digest under a pepper: a random key of 32 bytes, held wherever the deployment keeps its secrets and never defaulted. Read one from configuration:

```lean
def pepper (keyId encoded : String) : Option Pepper :=
  (Leancrypto.Codec.Base64Url.decodeString encoded).map fun secret => { keyId := ⟨keyId⟩, secret }
```

To rotate, make the new pepper current and keep the old one in the ring:

```lean
def rotated (current previous : Pepper) : PepperRing :=
  { current, retired := [previous] }
```

A session is digested once, when it is issued, so the old pepper has to stay until every session it minted has expired: `sessionAbsoluteLifetime`, 90 days by default. Dropping it sooner signs those people out.

## Sending mail

Postmark is above; Amazon SES takes a region and credentials, including the session token of an assumed role:

```lean
def ses (credentials : Aws.Sigv4.Credentials) : EmailTransport IO :=
  Ses.transport { region := "eu-west-1", credentials }
```

The `From` domain needs all of these before mail is delivered rather than filed:

- **SPF** authorising the provider's servers.
- **DKIM** with the provider's selector.
- **DMARC** on the organisational domain, tested at `p=none` first.
- **MX** on the sending subdomain: a real one, or an explicit null MX (`0 .`, RFC 7505).

A send that fails looks to the person who asked exactly like one that worked, so a sender identity nobody verified fails in silence unless you observe it. `observeSendFailure` is told the tenant, which mail it was with its attempt or invitation id, and the error, whose detail carries the provider's own error code. It is not told the address:

```lean
def logSendFailures (ports : Service.Ports IO) : Service.Ports IO :=
  { ports with
    observeSendFailure := some fun tenant kind error =>
      IO.eprintln s!"send failed in {tenant.value}: {repr kind}: {repr error}" }
```

## Bounces

Without bounce handling, a mistyped address keeps being sent sign-in mail and your sending reputation pays for it. Give each transport's endpoint to the routes:

```lean
def webhooks (hookPassword bouncesTopicArn : String) : List (WebhookEndpoint IO) :=
  [ Postmark.endpoint { username := "hook", password := hookPassword },
    Ses.endpoint (Ses.curlSubscription [bouncesTopicArn]) ]
```

Each answers on `/t/<tenant>/webhooks/<name>` and verifies a callback before reading it. A hard bounce or a spam complaint suppresses the address in that tenant, and suppressed addresses are refused before the transport is asked. Name every SNS topic you expect, since an empty list accepts nothing, and set those topics to signature version 2. `Service.suppressed`, `Service.clearSuppression` and `Service.deliveryReport` are the operations a support page needs.

## In front of the routes

```lean
def app (ports : Service.Ports IO) (hookPassword bouncesTopicArn : String) :
    Routing.StatelessHandler .std :=
  Middleware.forwardedRemoteAddr Middleware.Header.Name.xForwardedFor <| Http.handler
    { ports
      tenant := fun t => pure (some (config t))
      webhooks := webhooks hookPassword bouncesTopicArn }
```

No route reads more than 1 MiB of a request body. The per-IP rate limit reads the source address that `Middleware.forwardedRemoteAddr` establishes and nowhere else, so name a header your proxy sets and a client cannot. Bot mitigation is the `HumanCheck` port: give `humanCheck` an implementation calling your provider, and set `Http.Config.humanProofField` to the form field its widget writes.

## What a refusal says

Before any mail is sent, there are only a few reasons to refuse: a malformed address, a rate limit or failed bot check (`throttled`), a suppressed address, and a tenant that does not offer the magic link. Whether an address has an account, or may create one, is decided only once the link is followed, so nothing the sign-in page says can reveal it.

By default every one of those shows "check your mail". Changing that is a product decision, and `SignInResponsePolicy` is where you make it. A malformed address or a rate limit says nothing about anybody's account, so both are safe to state:

```lean
def candid : SignInResponsePolicy IO :=
  { respond := fun _ outcome => pure <|
      match outcome with
      | .malformedAddress => { message := .addressMalformed }
      | .throttled => { message := .tryAgainLater }
      | _ => { message := .checkYourMail } }
```

A suppressed address is different: saying so tells whoever typed it that the mailbox bounced. Whatever the policy says, the status, headers and timing of the response stay the same, and the audit log records the true outcome.

## Housekeeping

```lean
def housekeeping (ports : Service.Ports IO) (tenants : List TenantId) : IO Unit := do
  for tenant in tenants do
    discard <| Service.purgeExpired (tenant := tenant) ports
```

This removes expired attempts and sessions so tables stop growing. Nothing depends on it for correctness, and the library never schedules it: run it from whatever does your periodic work. The audit log, consent records and delivery history are never removed.
