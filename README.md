# lean-auth

Passwordless authentication for Lean 4 web applications: magic links with a cross-device
verification code, per-tenant signup policy, invitations, and sessions.

`REQUIREMENTS.md` is the specification. `KNOWN_ISSUES.md` records where the implementation
falls short of it and why.

## State of the implementation

Stage 1 of the delivery order in REQUIREMENTS §19: the domain model, the pure state machine,
and the theorems of AUTH-16.1. There is no IO, no storage, and no HTTP; every module here is
total pure Lean.

- `Authentication/Attempt.lean` is the centre. `begin` and `step` decide a sign-in from an
  explicit state and an event, and return the next state together with the effects the edge is
  to perform. Time, randomness, and the digests of whatever a request offered arrive as
  arguments; nothing in this layer performs an effect.
- `Authentication/Email.lean` parses and normalises addresses, and holds a domain as its
  labels, which is what makes allowlist matching respect label boundaries.
- `Authentication/Codec/` holds base64url and Crockford base32.
- The rest is the domain model: tenants, digests, configuration, accounts, invitations,
  signup policy, audit records, and the sign-in response policy.

Identifiers are indexed by the tenant they belong to (`AccountId tenant`), so an expression
that crosses tenants does not typecheck.

Still to come, in the order REQUIREMENTS §19 gives: the `AuthStore` port and its conformance
suite, the shared SQL backend with Postgres and SQLite, the Postmark transport, invitations and
signup policy wired end to end, OIDC, and the session management surface.

## Building

```
lake build
lake test
```

Warnings are errors. Most of the suite is theorems, which pass by compiling; `lake test` runs
the worked cross-device flow, whose value is in the effects a theorem does not constrain.
