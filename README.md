# lean-auth

Passwordless authentication for Lean 4 web applications: magic links with a cross-device
verification code, per-tenant signup policy, invitations, and sessions.

`REQUIREMENTS.md` is the specification. `KNOWN_ISSUES.md` records where the implementation
falls short of it and why.

## State of the implementation

Stages 1 to 6 of the delivery order in REQUIREMENTS §19: the domain model and pure state machine
with the theorems of AUTH-16.1, then the `AuthStore` port, its conformance suite, the SQLite
backend, and the cross-device flow running end to end with no server, then one SQL
implementation shared by both backends, with Postgres and SQLite each passing the suite, then
the Postmark transport, then signup policy and invitations, then the SES transport.

- `Authentication/Attempt.lean` is the centre. `begin` and `step` decide a sign-in from an
  explicit state and an event, and return the next state together with the effects the edge is
  to perform. Time, randomness, and the digests of whatever a request offered arrive as
  arguments; nothing in this layer performs an effect.
- `Authentication/Service.lean` is the interpreter at the edge. It mints credentials, reads and
  writes through the store, and performs those effects. It takes no decisions.
- `Authentication/Store.lean` is the storage port, and `Authentication/Store/Conformance.lean`
  is the suite any backend must pass. The suite ships with the library so third parties can run
  it against their own backends.
- `Authentication/Email.lean` parses and normalises addresses, and holds a domain as its
  labels, which is what makes allowlist matching respect label boundaries.
- `leancrypto` supplies base64url, Crockford base32, hex, SHA-256 and HMAC-SHA256. `Pepper`
  is what this library adds to them: the server-side key a credential is digested under, and the
  ring of keys a lookup may be satisfied by while a rotation overlaps.
- `AuthenticationSql/` is one implementation of the port for every SQL backend. A statement is
  a list of fragments and a value can enter one only as a parameter, so no path exists by which
  a value reaches the SQL text. What a backend supplies is a dialect, a schema, and an adapter.
- `AuthenticationSqlite/` and `AuthenticationPostgres/` are those backends, each in its own
  target because the core library depends on no driver.
- `AuthenticationPostmark/` and `AuthenticationSes/` are the two outbound transports, each in its
  own target for the same reason. Nothing provider-specific appears outside them, and two of them
  is what makes the port an abstraction rather than a description of one provider. SES is reached
  through the SESv2 API signed with SigV4 from `leanaws`, rather than through its SMTP endpoint,
  because the API reports its failures in a form the permanent and transient split can read.

Identifiers are indexed by the tenant they belong to (`AccountId tenant`), so an expression
that crosses tenants does not typecheck.

Still to come, in the order REQUIREMENTS §19 gives: rate limiting, and the session management
surface. Federated sign-in over OIDC is deferred; REQUIREMENTS §6 keeps the
requirements for it.

## Applying the schema

The package ships the SQL under `migrations/postgres` and `migrations/sqlite`, paired up and down
and named in `leanmigrate`'s convention, so a client using `leanmigrate` copies the files into its
own migrations directory and they run in with everything else. Applying them by any other means,
`psql`, the `sqlite3` shell, a deployment pipeline, works just as well: they are ordinary SQL.

Postgres objects live in an `auth` schema and SQLite objects behind an `auth_` prefix, so they
cannot collide with a client's own. Both stay in the client's database, which is what makes
enlisting in the client's transaction possible at all.

**Applying them is yours, and nothing here checks that you did.** The library does not run
migrations and does not record or verify that they ran. A client who upgrades and forgets finds
out when a statement first names a column the database does not have, which is later and less
obvious than a failure at startup. `KNOWN_ISSUES.md` records why the alternative was judged more
machinery than the problem justifies.

`Sqlite.openInMemory` applies the schema, because it starts empty every time and the tests run
against it. `Sqlite.openFile` deliberately does not.

## Sending domain DNS

The `From` domain needs all of these before it will be delivered rather than filed (AUTH-10.8):

- **SPF** on the sending domain, authorising the provider's servers.
- **DKIM** on the sending domain, with the provider's selector, so the signature survives
  forwarding.
- **DMARC** on the organisational domain, with an alignment policy you have tested at `p=none`
  before moving to `p=quarantine` or `p=reject`.
- **MX** on the sending subdomain: either a real one, or an explicit null MX (`0 .`, RFC 7505)
  saying it accepts no mail. A `From` domain with no MX record at all is penalised by receivers
  who read the absence as misconfiguration rather than intent.

The last one is the one that gets missed, because mail sends fine without it until a receiver
starts scoring it.

## Building

```
lake build
lake test
```

The tests are a subproject in `test/` with its own lakefile, which the top-level `lake test`
calls. They are not part of the package this library publishes, so a project depending on it is
free to name its own modules `Tests.*` and acquires nothing the library does not ship.

Warnings are errors. Most of the suite is theorems, which pass by compiling; `lake test` runs
the worked cross-device flow, whose value is in the effects a theorem does not constrain.

`lake test` needs `libpq` to build and a Postgres server to run against, because the reference
backend has to pass the conformance suite for the suite to mean anything. It connects to
`dbname=leanauthentication user=leanauthentication` unless `AUTHENTICATION_POSTGRES` says
otherwise, creates its own schema, and reports an unreachable server as a failed check rather
than skipping.
