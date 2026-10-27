# lean-authentication

- Passwordless authentication for Lean 4 web applications: magic links with a cross-device verification code, per-tenant signup policy, invitations, sessions, bounce handling, and consent records.
- Federated sign-in with OpenID Connect providers, plus Apple and GitHub.
- Passkeys: WebAuthn registration and sign-in, discoverable credentials only.
- An OAuth 2.1 authorisation server.

This library handles authentication only, not roles or permissions or any other form of authorisation.

For an example of this in use, see [TodoMVC Max](https://github.com/paulbutcher/lean-todomvc-max).

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
| `AuthenticationFetch` | Outbound document fetch, with the rules that make one safe |
| `AuthenticationOidc` | Federated sign-in: OpenID Connect, Apple, and non-OIDC providers (needs OpenSSL) |
| `AuthenticationOidcHttp` | Ready-made federated sign-in routes |
| `AuthenticationPasskey` | Passkeys: WebAuthn verification (needs OpenSSL) |
| `AuthenticationPasskeyHttp` | Ready-made passkey routes, answering JSON |

## Using it

[docs/](docs/README.md) sets out which use cases are supported, from open self-signup to enforced single sign-on, and has a guide for each. [Getting started](docs/getting-started.md) has email sign-in running on your own machine in a few minutes.

## Guarantees

- **Tenant isolation is typed.** Identifiers carry their tenant (`AccountId tenant`), so an expression crossing tenants does not compile.
- **No credential is stored.** Magic tokens, codes, session identifiers and invitation tokens are held as HMAC digests under a server-side pepper. Rotation has an overlap window.
- **One attempt is live per address**, and starting a second abandons the first atomically. Magic tokens are single use; code entry is capped at five tries.
- **A link opened on another device signs nobody in on that device.** Completion always requires the browser holding the attempt cookie.
- **Sign-in responses say nothing by default.** Every outcome maps to the same message, and the shipped routes give every outcome the same status, headers and one `Set-Cookie`, including outcomes that began no attempt. `ResponseFloor` normalises the latency.
- **Rate limiting counts five scopes**: per (tenant, address), per address across all tenants, per source IP, per tenant, and globally.
- **Provider callbacks are verified inside the endpoint**, before the payload is read. The SNS certificate is fetched only from a recognised host, decided before the fetch, and the topic is checked.
- **`returnTo` is validated** against the tenant's allowlist before any redirect. It travels as a URI reference in its encoded form: a caller with a target whose own query holds encoded values encodes the whole reference once for the form field, and what reaches the browser is that reference, escaped only where a header value could not otherwise hold it.
- **The audit log and the consent history are append only.** The port offers no update or delete.
- **A passkey signs in the account its own credential belongs to**, and only where the user handle the authenticator offered names that account or is absent. A theorem, and the biconditional form of it: nothing reaches a sign-in that is not one of those two cases.
- **A recovery grant enrols one credential and issues no session**, on the account named on the grant and never one named in the request. It is single use under compare-and-set, spent when the credential is written rather than when the ceremony begins, and issuing one signs the account out everywhere.
- **An authorization code is redeemed at most once**, a refresh token rotated at most once, and either presented twice revokes everything its grant issued. Both are theorems about the state and compare-and-set in the store.
- **A token's audience is the `resource` its request named**, and its scopes are a subset of what was consented to. Both are theorems, and verification refuses a token presented anywhere else.
- **A redirect URI is compared as a string**, with the port ignored for loopback URIs and for nothing else. That the exception admits no other host is a theorem.

[REQUIREMENTS.md](REQUIREMENTS.md) is the specification, and [KNOWN_ISSUES.md](KNOWN_ISSUES.md) records where the implementation deliberately falls short of it.

## Building

```
lake build
lake test
```

Tests are a subproject in `test/` with its own lakefile, so a project depending on this one is free to name its own modules `Tests.*`. Warnings are errors.

`lake test` needs `libpq` and a Postgres server. It connects to `dbname=leanauthentication user=leanauthentication` unless `AUTHENTICATION_POSTGRES` says otherwise, and reports an unreachable server as a failed check rather than skipping.
