# lean-auth

Passwordless authentication for Lean 4 web applications: magic links with a cross-device
verification code, per-tenant signup policy, invitations, and sessions.

`REQUIREMENTS.md` is the specification. `KNOWN_ISSUES.md` records where the implementation
falls short of it and why.

## State of the implementation

Stages 1 to 3 of the delivery order in REQUIREMENTS §19: the domain model and pure state machine
with the theorems of AUTH-16.1, then the `AuthStore` port, its conformance suite, the SQLite
backend, and the cross-device flow running end to end with no server, then one SQL
implementation shared by both backends, with Postgres and SQLite each passing the suite.

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
- `Authentication/Codec/` and `Authentication/Crypto/` hold base64url, Crockford base32,
  SHA-256 and HMAC-SHA256. See `KNOWN_ISSUES.md` for why they are here.
- `AuthenticationSql/` is one implementation of the port for every SQL backend. A statement is
  a list of fragments and a value can enter one only as a parameter, so no path exists by which
  a value reaches the SQL text. What a backend supplies is a dialect, a schema, and an adapter.
- `AuthenticationSqlite/` and `AuthenticationPostgres/` are those backends, each in its own
  target because the core library depends on no driver.

Identifiers are indexed by the tenant they belong to (`AccountId tenant`), so an expression
that crosses tenants does not typecheck.

Still to come, in the order REQUIREMENTS §19 gives: the Postmark transport, signup policy and
invitations wired through, OIDC, and the session management surface. Rate limiting is required
and is not in any stage; see `KNOWN_ISSUES.md`.

## Building

```
lake build
lake test
```

Warnings are errors. Most of the suite is theorems, which pass by compiling; `lake test` runs
the worked cross-device flow, whose value is in the effects a theorem does not constrain.

`lake test` needs `libpq` to build and a Postgres server to run against, because the reference
backend has to pass the conformance suite for the suite to mean anything. It connects to
`dbname=leanauthentication user=leanauthentication` unless `AUTHENTICATION_POSTGRES` says
otherwise, creates its own schema, and reports an unreachable server as a failed check rather
than skipping.
