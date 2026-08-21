# lean-auth requirements

Requirements for a reusable Lean 4 library providing passwordless authentication for web
applications. Written to be handed to an implementer working in a freshly created package
(`lake new lean-auth lib`). The name `lean-auth` is a placeholder; confirm it before publishing.

Requirement keywords: **MUST**, **SHOULD**, **MAY**. Requirements are numbered so that
implementation and review can refer to them.

---

## 1. Purpose and scope

`lean-auth` authenticates people for web applications without passwords. It provides:

- Email-based sign-in using a magic link, with a cross-device verification code.
- Optional classic email one-time codes.
- Per-tenant signup policy: open, domain-restricted, or invitation-only.
- Session issue, inspection, and revocation.
- A pluggable outbound email transport, with Postmark and Amazon SES as the first
  implementations.
- Pluggable storage, with Postgres and SQLite as the first implementations.

### 1.1 Non-goals for the first version

- Passwords, in any form. There is no password field, no reset flow, no hashing of secrets
  the user chose.
- Federated sign-in over OAuth 2.0 / OpenID Connect. Deferred; see §6, which remains specified
  against the day it is built.
- Authorisation. The library says who someone is, not what they may do. See §13, which is a
  requirement rather than a note: the boundary shapes the API.
- Self-service account recovery. Someone who loses access to their mailbox is recovered by
  administrator action in the host application. See §18.1.
- Inbound email processing. See §11.
- SAML and SCIM. See §18.4; the model must not preclude them later.
- Passkeys / WebAuthn. See §18.3; the credential model must not preclude them later.
- SMS or any telephony.

---

## 2. Target environment

- **AUTH-2.1** Toolchain `leanprover/lean4:v4.33.0`, matching the ecosystem libraries below.
- **AUTH-2.2** The core library MUST NOT depend on any HTTP server framework, nor on any
  database driver. Framework and driver bindings live in separate `lean_lib` targets so that
  the core is usable with either and requires neither.
- **AUTH-2.3** Expected dependencies, all from `github.com/paulbutcher` unless noted:
  - `leancurl` for outbound HTTPS (the Postmark and SES APIs).
  - `leancrypto` for SHA-256, HMAC-SHA256, hex, base64 and base64url, Crockford base32, the byte
    comparison of AUTH-5.3.4, and, for AUTH-12.1.2, RSASSA-PKCS1-v1_5 verification with the DER
    reader that gets a public key out of a certificate.
  - `leanpostgres` for the Postgres storage backend. Not `leanmigrate`: the migrations this
    library ships are SQL files the client applies, so nothing here depends on a migration tool
    (AUTH-15.7.1).
  - A SQLite driver, for both the SQLite backend and the test backend (AUTH-16.5), which makes
    it a dependency of `lake test` and not only of one optional target. Confirm what exists in
    the ecosystem before depending on it; if nothing suitable does, stop and ask rather than
    writing one here.
  - `lean-telemetry` for tracing and metrics.
  - `lean-routing`, `lean-html` and `lean-middleware` for the optional HTTP integration target
    only. `lean-forms` and `lean-htmx` were expected here too and are not used: `Middleware`
    already decodes a form body, and nothing the sign-in routes do needs a partial page update.
  - `plausible` (leanprover-community) for property tests.
- **AUTH-2.4** Any cryptography needed (HMAC-SHA256, SHA-256, base64url, constant-time
  comparison, and the AWS Signature Version 4 derivation built on the first two) MUST be
  surveyed against the existing ecosystem before being written here. If it does not exist, stop
  and ask whether it belongs in a new shared library rather than in `lean-auth`. Do not vendor a
  copy. The survey was done and found nothing usable, so `leancrypto` was created to hold these
  and this library depends on it; a further consumer needing the same primitives extends that
  library rather than reopening the question. ES256 and RS256 signature verification are deferred
  with §6.

---

## 3. Architecture

The single most important structural requirement:

- **AUTH-3.1** All authentication logic MUST be expressed as pure total functions over an
  explicit state type. Effects (time, randomness, storage, HTTP, email) MUST be represented as
  data returned by those functions, and performed by a thin interpreter at the edge.

  The intended shape:

  ```
  def step (cfg : TenantConfig) (now : Timestamp) (s : AttemptState) (e : AttemptEvent)
    : Except AuthError (AttemptState × List Effect)
  ```

  This is what makes the security properties in §16 provable rather than merely tested. An
  implementation that reaches for `IO` inside the state machine has failed this requirement.

- **AUTH-3.2** Every external dependency MUST be reached through a port, with at least two
  implementations: the real adapter and one usable by tests without network access. The ports
  are `Clock`, `RandomBytes`, `AuthStore`, `RateLimiter`, `EmailTransport`, `HttpClient`, and
  `SignInResponsePolicy`.
- **AUTH-3.3** `Clock` and `RandomBytes` MUST be ports rather than direct `IO` calls, so tests
  can pin time and seed randomness.
- **AUTH-3.4** No authentication state may live in process memory. Every instance of the host
  application MUST be able to serve any request in any flow. This applies to login attempts,
  OAuth `state` records, sessions, and rate-limit counters.
- **AUTH-3.5** Ports whose implementation is selected from configuration at startup
  (`AuthStore`, `RateLimiter`, `EmailTransport`, `SignInResponsePolicy`) MUST be structures the
  client constructs and passes explicitly, not typeclasses. The choice is a runtime one and
  typeclass resolution is not. Ports resolved statically (`Clock`, `RandomBytes`) MAY be
  typeclasses.

---

## 4. Tenancy and domain model

### 4.1 The two levels

- **AUTH-4.1.1** A **client** is one host application wiring the library in. It supplies the
  ports, the templates, and the response policy. There is one client per deployment of a host
  application.
- **AUTH-4.1.2** A **tenant** is one organisation within a client. A client MUST support many
  tenants. All configuration that varies by organisation (signup policy, sending identity,
  session lifetimes, enabled identity providers) belongs to the tenant.
- **AUTH-4.1.3** The library MUST NOT own the tenant concept beyond an opaque `TenantId` it
  treats as a foreign key, plus its own per-tenant configuration record. The tenant's name,
  billing, and everything else belong to the client.

### 4.2 Accounts are scoped to the tenant

- **AUTH-4.2.1** An `Account` is identified by the pair (tenant, email). The same address in two
  tenants is two independent accounts with no shared state, no shared sessions, and no shared
  credentials. A person who wants access to two tenants verifies their address twice.
- **AUTH-4.2.2** There is no membership relation and no tenant-selection step. A session belongs
  to exactly one account and therefore to exactly one tenant.
- **AUTH-4.2.3** A linked external identity is keyed on (tenant, issuer, subject). The same
  Google account signing into two tenants produces two accounts.
- **AUTH-4.2.4** Every store operation MUST take a `TenantId`, and it MUST be impossible to
  express a query that returns rows from another tenant. Prefer a type-level guarantee, for
  example by making the identifier types carry the tenant, over a discipline the caller has to
  remember.
- **AUTH-4.2.5** Deleting a tenant MUST remove its accounts, sessions, invitations, attempts,
  suppression entries, consent records, and audit records, with no orphans.

### 4.3 Tenant identification in URLs

- **AUTH-4.3.1** Every sign-in entry point MUST identify the tenant. A bare "enter your email"
  page with no tenant context is not implementable, since the same address means different
  accounts in different tenants.
- **AUTH-4.3.2** For v1, tenants are distinguished by a path prefix on a single shared origin
  (`/t/<tenant>/...`). Rationale: OAuth providers require exact-match registered redirect URIs,
  so a per-tenant hostname would need one registration per tenant, or a shared callback origin
  plus a cross-origin handoff credential. Neither is worth building before it is needed.
- **AUTH-4.3.3** Session and attempt cookies MUST be scoped to the tenant, so that one browser
  can hold concurrent sessions in several tenants without collision. With path-based tenancy
  this is `Path=/t/<tenant>`. Path scoping is not a security boundary, and is not asked to be
  one here: both tenants run the same application code.
- **AUTH-4.3.4** Every URL the library emits (magic links, OAuth redirect targets, post-sign-in
  redirects) MUST be built from a per-tenant base URL held in configuration, never from a
  global constant. In v1 every tenant's base URL resolves to the same origin. This is what makes
  per-tenant hostnames a configuration change later rather than a rewrite.
- **AUTH-4.3.5** A base URL MUST be accepted with or without a trailing slash on its origin, and
  a trailing slash MUST NOT reach a URL built from it. Every path the library appends begins with
  a slash, so `https://app.example.com/` would otherwise produce an empty leading path segment
  matching no route, in a magic link already sent. Platforms publish origins both ways, an AWS
  Lambda function URL among them, so the wrong form is the one a client is invited to copy. Only
  trailing slashes are removed: an origin carrying a path prefix keeps it. An origin of nothing
  but slashes becomes empty, and the URL then lacks a scheme and host rather than looking usable.

### 4.4 Account structure

- **AUTH-4.4.1** An `Account` has one **primary email**, zero or more **verified additional
  emails**, and zero or more **linked identities**.
- **AUTH-4.4.2** `Credential` is deliberately open: the store MUST model an account's means of
  proving identity as a set, not as fixed columns, so that a passkey or a second factor can be
  added later without a schema rewrite.
- **AUTH-4.4.3** `LoginAttempt` is the record of one sign-in in progress. Its states are exactly:
  `pending`, `revealed`, `completed`, `expired`, `abandoned`.
- **AUTH-4.4.4** `Invitation` is a grant on one specific email address within one tenant.
- **AUTH-4.4.5** `Session` is an issued authentication for one account on one user agent.

### 4.5 Email address handling

- **AUTH-4.5.1** Addresses MUST be parsed into local part and domain, rejecting anything with no
  `@`, more than one unquoted `@`, an empty part, or a trailing dot on the domain.
- **AUTH-4.5.2** The domain MUST be normalised to lowercase ASCII, converting internationalised
  domains to punycode before storage or comparison. Two addresses that differ only in domain
  case or IDN encoding are the same address.
- **AUTH-4.5.3** The local part MUST be preserved verbatim for sending, and compared
  case-insensitively for identity. Rationale: SMTP permits case-sensitive local parts, but no
  real provider uses them, and treating them as distinct produces duplicate accounts.
- **AUTH-4.5.4** Plus-tag and dot stripping (`user+tag@`, `u.s.e.r@gmail.com`) MUST NOT be
  applied by default. It MAY be offered as an explicit per-tenant option, off unless configured,
  because it silently merges addresses that some organisations treat as distinct.

### 4.6 Consent records

Answering §18.7. Terms acceptance and marketing consent are recorded here; they are not captured
here, and the distinction is the whole of the design.

- **AUTH-4.6.1** The library MUST NOT solicit consent anywhere in the sign-in flow. Whether a
  sign-in is about to create an account is exactly what §14.2 exists to hide, and a control shown
  only to addresses with no account reports it before any mail is sent, to anyone who reads the
  page. The client asks somebody it has already authenticated, at a moment of its choosing, and
  records the answer. A consequence to state plainly: consent is therefore not captured at the
  instant of signup, which is what §18.7 asked for in so many words.
- **AUTH-4.6.2** A record MUST carry the subject consented to, the version that was shown, the
  answer, and when it was given. The subject and the version are the client's own strings, stored
  verbatim and never interpreted, as an invitation's metadata is (AUTH-8.7). The library records
  that something was agreed to, not what.
- **AUTH-4.6.3** The history MUST be append only. Withdrawing MUST add an entry rather than edit
  or remove the one that granted, so that what was agreed to under an earlier version stays on
  the record. The store MUST offer no update and no delete for it.
- **AUTH-4.6.4** Where a subject stands now MUST be derived from the last entry about it.
  Withdrawal has to be as easy as granting, so a later withdrawal MUST take precedence over any
  earlier grant, and a subject with no entry MUST NOT count as granted.
- **AUTH-4.6.5** The library MUST expose, per tenant, the accounts whose latest answer on a
  subject was a grant. This is the query a mailshot is drawn from, and leaving it to the client to
  fold every account's history is leaving the mistake that mails somebody who said no.
- **AUTH-4.6.6** Consent records MUST NOT be swept (AUTH-15.4.3). They outlive the attempts and
  sessions around them because their purpose is evidentiary, and how long they are kept is part of
  the retention question in §18.5.
- **AUTH-4.6.7** Distinct consents MUST be recordable separately, not as one answer. A single
  control covering both terms and marketing invalidates the marketing half under the usual reading
  of GDPR Article 7(4).

---

## 5. Email sign-in: the magic link flow

This is the primary flow and the one with the most subtle requirements. Read the whole section
before implementing any of it.

### 5.1 The shape of the flow

1. The person enters their email on a tenant's sign-in page in **browser A** and submits.
2. The server creates a `LoginAttempt` in state `pending`, generates a magic token and a
   verification code, and sets an **attempt cookie** on browser A.
3. The server sends an email containing a link carrying the magic token.
4. Browser A displays a page saying that mail has been sent, containing a field for a
   verification code.
5. When the link is opened:
   - **Same device**: the attempt cookie is present and matches. The landing page offers a
     button to finish signing in. Pressing it completes the attempt and issues a session to
     that browser.
   - **Different device**: no matching cookie. The landing page displays the verification code
     and instructs the person to type it into the browser where they started. It MUST NOT issue
     a session on the device that opened the link.
6. The person types the code into browser A. On success the attempt completes and browser A
   receives a session.

### 5.2 Requirements

- **AUTH-5.2.1** Opening the magic link MUST be a `GET` that issues no session and consumes no
  credential. Completing sign-in MUST require a `POST` from the landing page. Rationale:
  corporate link scanners and mail clients prefetch URLs; a `GET` that logs someone in or burns
  the token makes the product unusable behind those gateways.
- **AUTH-5.2.2** The `pending` to `revealed` transition MUST be idempotent. Repeatedly opening
  the link before expiry MUST show the same code and MUST NOT invalidate the attempt.
- **AUTH-5.2.3** Same-device detection MUST rely on the attempt cookie only. User agent
  strings, IP addresses, and fingerprints MUST NOT be used to decide it. They are unreliable
  and their failure mode is locking people out.
- **AUTH-5.2.4** The attempt cookie MUST be `Secure`, `HttpOnly`, `SameSite=Lax`, scoped to the
  tenant path per AUTH-4.3.3, and expire with the attempt. `Lax` is required and not an
  oversight: the cookie has to survive a top-level navigation arriving from a mail client, and
  `Strict` would make every same-device click look cross-device.
- **AUTH-5.2.5** The attempt cookie MUST contain a binding nonce that is checked against the
  attempt record. Possessing an attempt id MUST NOT be sufficient to be treated as the
  originating browser.
- **AUTH-5.2.6** The verification code MUST be accepted only from a request carrying the
  matching attempt cookie, and only while the attempt is in state `revealed`.
- **AUTH-5.2.7** Code entry MUST be limited to 5 attempts per login attempt. On the sixth, the
  attempt moves to `abandoned` and both the code and the magic token stop working.
- **AUTH-5.2.8** Attempt lifetime MUST default to 15 minutes and be configurable per tenant
  within a bounded range. Completion MUST be rejected after expiry regardless of state.
- **AUTH-5.2.9** At most one attempt per (tenant, address) may be `pending` or `revealed`.
  Creating a new one MUST move any existing one to `abandoned`. Rationale: without this, an
  attacker can farm concurrent attempts to multiply the code guess budget.
- **AUTH-5.2.10** Browser A SHOULD poll or subscribe for attempt completion, so that a
  same-device click in another tab updates the tab where the flow began.
- **AUTH-5.2.11** The email MUST name the tenant prominently, in the subject and the body.
  Someone with accounts in several tenants otherwise receives indistinguishable messages and
  cannot tell which organisation they are authorising.
- **AUTH-5.2.12** The email MUST state the requesting IP address, approximate location if
  available, and time, and MUST tell the recipient what to do if they did not request it. It
  MUST NOT contain any content supplied by the requester.

### 5.3 Credential strength

- **AUTH-5.3.1** The magic token MUST be at least 128 bits from a cryptographically secure
  source, encoded base64url.
- **AUTH-5.3.2** The revealed verification code MUST be at least 40 bits, rendered in an
  alphabet excluding visually confusable characters (Crockford base32 is suitable), and
  displayed in groups for transcription.
- **AUTH-5.3.3** If classic emailed codes are enabled (§5.4), that code MUST be at least 6
  digits and is protected by rate limiting and the attempt lifetime rather than by entropy
  alone.
- **AUTH-5.3.4** All credentials MUST be stored as HMAC-SHA256 digests under a server-side
  pepper, never in clear. Comparison MUST be constant-time. Each stored digest MUST carry the
  identifier of the key that produced it (AUTH-15.7.2).
- **AUTH-5.3.5** Consuming a credential MUST be atomic in the store: a compare-and-set or a
  conditional update, never read-then-write. Two concurrent completions of the same attempt MUST
  produce exactly one session.

### 5.4 Optional classic one-time code

- **AUTH-5.4.1** A tenant MAY be configured to also place a typed code in the email body, for
  people who prefer typing to clicking and for mail environments that mangle links.
- **AUTH-5.4.2** When enabled, that code is a distinct credential from the revealed code. Both
  are valid inputs to the same attempt; both are subject to the shared 5-attempt budget.
- **AUTH-5.4.3** Where the library serves the sign-in pages, enabling this MUST give the person
  somewhere to type the code. The two codes MUST be submitted separately rather than one
  endpoint trying both, because a submission tried against both spends two entries of the budget
  they share.

---

## 6. Federated sign-in (OAuth 2.0 / OIDC)

Deferred out of the first version. The section is retained in full, both so that later
requirement numbers stay stable and because the requirements below were written while the
reasoning behind them was fresh; AUTH-6.7 in particular is the account takeover that is easy to
reintroduce from a blank page.

Requirements elsewhere that presuppose federated sign-in are deferred with it: AUTH-6.10,
AUTH-8.6, AUTH-14.2.7, AUTH-15.7.3, the OAuth state record of §15.1, and the
unverified-provider-email case of AUTH-16.7. What is not deferred
is the provision made for it, which is cheap now and expensive to retrofit: the `SignInOutcome`
type of AUTH-14.2.1 and the response policy of §14.2 are shared surfaces that a federated path
must join rather than duplicate, and AUTH-4.4.2 keeps `Credential` open so that a linked identity
needs no schema rewrite.

- **AUTH-6.1** The Authorization Code flow with PKCE (`S256`) MUST be used, including for
  confidential clients. The implicit and hybrid flows MUST NOT be implemented.
- **AUTH-6.2** `state` MUST be a random value bound to a server-side record holding the tenant,
  the return target, and the creation time. It MUST be single use and expire within 10 minutes.
  Carrying the tenant in `state` is required from the start, even though v1 uses one origin, so
  that a single registered redirect URI serves every tenant.
- **AUTH-6.3** `nonce` MUST be sent and MUST be checked against the returned ID token.
- **AUTH-6.4** Provider metadata MUST be obtained from the issuer's discovery document, and JWKS
  MUST be cached with lookup by `kid`. An unknown `kid` triggers at most one refetch, rate
  limited so that a malicious token cannot drive unbounded outbound requests.
- **AUTH-6.5** ID token validation MUST check signature, `iss`, `aud`, `exp`, `iat`, and
  `nonce`, with clock skew tolerance of at most 60 seconds. Tokens failing any check MUST be
  rejected with no partial account creation.
- **AUTH-6.6** An external identity MUST be keyed on (tenant, issuer, subject). It MUST NOT be
  keyed on email address; providers permit address changes and subjects are the stable key.
- **AUTH-6.7 (account linking, security critical)** An external identity MUST be linked to an
  existing account only when the provider asserts an email address that is marked verified by
  that provider and matches a verified address on the account, within the same tenant. Linking
  on an unverified provider email is the classic account takeover and MUST be impossible,
  including by configuration.
- **AUTH-6.8** Unlinking MUST be refused when it would leave an account with no usable means of
  signing in.
- **AUTH-6.9** Provider-specific behaviour that MUST be handled:
  - **Google**: require `email_verified`. The `hd` claim MAY be used as supporting evidence for
    a Workspace domain but the address domain is still checked per §7.
  - **Apple**: the client secret is an ES256 JWT minted from a `.p8` key with a bounded
    lifetime, so the adapter MUST mint it on demand rather than hold a static secret. The
    response arrives by `form_post`, which the integration layer must accept. The person's name
    is supplied only on first authorisation and MUST be captured then or lost. Private relay
    addresses (`@privaterelay.appleid.com`) are deliverable and MUST be accepted, but MUST NOT
    satisfy a domain allowlist.
  - **Non-OIDC OAuth providers** such as GitHub require a separate profile call and a separate
    call for verified addresses. The port MUST accommodate this without pretending they are
    OIDC.
- **AUTH-6.10** The signup policy of §7 applies identically to federated sign-in, and its
  outcome goes through the response policy of §14.2. A federated sign-in that is not permitted
  to create an account MUST NOT create a dormant or partial account.

---

## 7. Signup policy

- **AUTH-7.1** Each tenant is configured with exactly one policy:

  ```
  inductive SignupPolicy
    | open
    | domainAllowlist (domains : List Domain) (includeSubdomains : Bool)
    | inviteOnly
  ```

- **AUTH-7.2** `open`: any well-formed address may create an account.
- **AUTH-7.3** `domainAllowlist`: an address may create an account only if its normalised domain
  matches an entry.
  - **AUTH-7.3.1** Matching MUST be on whole labels. `evilexample.com` MUST NOT match
    `example.com`. This is the failure that turns a domain restriction into no restriction, and
    it is one of the theorems required in §16.
  - **AUTH-7.3.2** When `includeSubdomains` is set, `mail.example.com` matches `example.com`,
    and matching still requires a label boundary.
  - **AUTH-7.3.3** Comparison happens after punycode normalisation, so a homograph domain cannot
    match.
- **AUTH-7.4** `inviteOnly`: an account may be created only by accepting an invitation.
- **AUTH-7.5** Whether an invitation overrides a domain allowlist MUST be a per-tenant boolean,
  defaulting to allowing the override. The two policies compose: a tenant may restrict
  self-signup to its own domains while still inviting named outsiders.
- **AUTH-7.6** Policy is evaluated at account creation only. Tightening a policy MUST NOT lock
  out existing accounts; removing access is an explicit action by the client.
- **AUTH-7.7** A rejected signup MUST be recorded in the audit log with its true reason,
  regardless of what the person was told (§14.2).

---

## 8. Invitations

- **AUTH-8.1** The client creates an invitation for exactly one email address in one tenant. The
  library performs no permission check; see §13.
- **AUTH-8.2** The invitation email contains a link carrying an invitation token of at least 128
  bits, stored hashed per AUTH-5.3.4.
- **AUTH-8.3 (security critical)** Accepting an invitation MUST create an account for the
  invited address in the invited tenant, and no other. Both MUST come from the invitation
  record, never from request input at accept time, and the address MUST NOT be editable in the
  accept form.
- **AUTH-8.4** Invitation acceptance MUST go through the same attempt machinery as §5, including
  the cross-device code. An invitation link opened on a phone must not sign anyone in on that
  phone.
- **AUTH-8.5** Invitations MUST be single use, MUST default to a 7-day lifetime, MUST be
  revocable, and MUST be resendable. Resending MUST rotate the token and invalidate the old one.
- **AUTH-8.6** An invited person MAY complete signup with a federated provider instead of email,
  provided the provider asserts the invited address as verified. The invitation is a grant on an
  address, not on a mechanism.
- **AUTH-8.7** An invitation MUST carry an opaque metadata payload that the library stores
  verbatim and returns on acceptance without interpreting it. This is how the client attaches
  its own roles to an invitation while keeping roles out of the library (§13.3).
- **AUTH-8.8** Accepting an invitation for an address that already has an account in that tenant
  MUST sign that account in and mark the invitation consumed, not create a duplicate.
- **AUTH-8.9** The library MUST expose listing of pending, accepted, expired, and revoked
  invitations for a tenant.

---

## 9. Sessions

- **AUTH-9.1** Sessions MUST be server-side records with an opaque identifier of at least 128
  bits, stored hashed. Self-contained signed-cookie sessions MUST NOT be used, because they
  cannot be revoked.
- **AUTH-9.2** The session cookie MUST be `Secure`, `HttpOnly`, `SameSite=Lax`, and scoped to
  the tenant path per AUTH-4.3.3.
- **AUTH-9.3** A new session identifier MUST be issued at every sign-in. An existing anonymous
  session MUST NOT be promoted in place.
- **AUTH-9.4** Sessions MUST have both an idle timeout and an absolute lifetime, configurable
  per tenant, defaulting to 14 days idle and 90 days absolute.
- **AUTH-9.4.1** Validating a session MUST slide its idle expiry, or the idle timeout is only a
  shorter absolute lifetime. Sliding it MUST NOT carry a session past its absolute lifetime. The
  write MAY be deferred until the recorded last-seen time is stale by a configurable interval, so
  that validation is not a write on every request; the consequence, which MUST be documented, is
  that a session may expire up to that interval earlier than its last use implies.
- **AUTH-9.5** An account holder MUST be able to list their sessions with user agent, coarse
  location, creation and last-seen time, and revoke any or all of them. Revocation MUST take the
  account the session is expected to belong to, not the session alone, so that a client passing an
  identifier through from a request cannot be made to sign out an account it did not name.
- **AUTH-9.5.1** Deactivating an account MUST also prevent a new session being issued to it. The
  revocation AUTH-9.6 requires means nothing if the next magic link signs the account back in.
- **AUTH-9.6** All sessions for an account MUST be revoked on: primary email change, account
  deactivation, and any recovery action.
- **AUTH-9.7** Validating a session MUST return the account id and its tenant, and nothing else.
  No roles, no flags, no permissions (§13.4).
- **AUTH-9.8** Post-sign-in redirect targets MUST be validated against a per-tenant allowlist of
  paths or origins. An unvalidated `returnTo` is an open redirect and a phishing amplifier.

---

## 10. Outbound email

- **AUTH-10.1** The port:

  ```
  structure OutboundEmail where
    from           : SendingIdentity
    to             : EmailAddress
    subject        : String
    textBody       : String
    htmlBody       : Option String
    replyTo        : Option EmailAddress
    headers        : List (String × String)
    idempotencyKey : String

  structure EmailTransport (m : Type → Type) where
    send : OutboundEmail → m (Except SendError SentMessageId)
  ```

- **AUTH-10.2** `SendingIdentity` MUST be resolved per tenant from the first version, even
  though every tenant initially resolves to the same operator domain. Storing one row per tenant
  that points at the shared default turns per-tenant sending domains into a data change later
  rather than schema and wiring surgery. See §18.2.
- **AUTH-10.3** `SendError` MUST distinguish permanent failures (address rejected, suppressed)
  from transient ones (timeout, rate limited, provider 5xx), because the caller's response
  differs: one is told to the person, the other is retried.
- **AUTH-10.4** Every message MUST carry an idempotency key derived from the attempt, so that a
  retry after an ambiguous timeout cannot send two codes for one attempt.
- **AUTH-10.5** Sending MUST NOT block the HTTP response beyond a short bounded timeout. A slow
  provider must degrade to "we are sending it" rather than a hung request.
- **AUTH-10.6** The Postmark adapter uses the transactional message stream with the server token
  in `X-Postmark-Server-Token`. Nothing Postmark-specific may appear outside the adapter module,
  and the core library MUST compile without it.
- **AUTH-10.7** Email bodies MUST be produced from templates that the client can override per
  tenant, with a plain text part always present. Templates MUST escape all interpolated values
  in the HTML part.
- **AUTH-10.8** Deployment documentation MUST state the DNS requirements: SPF, DKIM, and DMARC
  on the sending domain, and either a real MX or an explicit null MX (RFC 7505) on the sending
  subdomain, so that receivers do not penalise a `From` domain that cannot receive mail.
- **AUTH-10.9** An Amazon SES adapter MUST be built in the first version, in its own target,
  and the core library MUST compile without either it or Postmark. The reasoning is AUTH-15.8.2's
  applied to this port: an abstraction with one implementation is not an abstraction, and the
  provider assumptions that have leaked into `OutboundEmail` are not visible until a second
  transport has to satisfy it.
- **AUTH-10.10** Both adapters MUST classify provider failures into the permanent and transient
  cases of AUTH-10.3 from the provider's own error vocabulary, not from the HTTP status alone.
  A failure an operator must fix, such as an unverified sending identity or an account still in
  the SES sandbox, is transient in this sense: it resolves without the person who asked for the
  link doing anything, and telling them their address was rejected would be false.
- **AUTH-10.11** The idempotency key of AUTH-10.4 MUST reach the provider by whatever channel
  that provider echoes back on its delivery and bounce notifications, so that the key preventing
  a double send is the key identifying the attempt when the bounce arrives (§12). It MUST NOT be
  dropped by an adapter whose provider has no idempotency header of its own.
- **AUTH-10.12** SES credentials MUST be supplied by configuration per AUTH-14.1.6, and the
  design MUST accommodate short-lived credentials carrying a session token, since an IAM role is
  the normal way to hold them and a long-lived access key is the thing deployment guidance
  should be able to discourage.
- **AUTH-10.13** SES MUST be reached through the SESv2 `SendEmail` API over HTTPS, signed with
  AWS Signature Version 4, rather than through its SMTP endpoint. The API gives the structured
  per-request errors AUTH-10.10 needs, carries email tags for AUTH-10.11, needs no SMTP client,
  and reaches the network through the same seam the Postmark adapter is tested through. The cost
  is request signing, which AUTH-10.14 places outside this library.
- **AUTH-10.14** SigV4 request signing MUST come from a separate shared library rather than being
  written in this repository. It is general-purpose AWS code with no connection to
  authentication, which is what AUTH-2.4 and AUTH-17.5 are about; a survey of the ecosystem found
  no Lean 4 implementation of it, and the nearest thing that exists, `paulbutcher/lean-aws-lambda`,
  wraps an application so it can run on Lambda rather than call an AWS API. Signing is a pure
  total function over a request and a timestamp, so it is testable against AWS's published
  vectors without a network and without this library.

---

## 11. Inbound email

Not in the first version. Retained as a section so that later requirement numbers stay stable.

Inbound processing was considered and deferred because no use case required it: the sign-in
flows are outbound only, and replies to authentication mail are handled by pointing `Reply-To`
at a mailbox or helpdesk the client already operates. If it returns, the design constraint worth
remembering is that the canonical inbound type must be a **parsed** message rather than raw
MIME, because Postmark delivers parsed JSON and offers no full raw MIME retrieval, so a
raw-MIME interchange type would make the first adapter impossible.

---

## 12. Bounces and suppression

- **AUTH-12.1** The library MUST ingest delivery events from every transport it ships (Postmark's
  bounce and spam-complaint webhooks, and SES's bounce and complaint notifications as SNS delivers
  them) and maintain a suppression list. Each adapter MUST normalise its provider's payload into
  one event type, so that the decision about which failures are permanent is taken once and not
  per provider.
- **AUTH-12.1.1** Establishing that a delivery event really came from the provider MUST happen
  before the event is read, and MUST NOT be a separate call a route could omit: a route holding an
  endpoint gets verified events or nothing. Postmark authenticates its webhooks with credentials
  on a URL the client chose; SNS signs its posts with a certificate the receiver fetches. An
  endpoint that skips this is one by which anyone who finds the URL decides which addresses stop
  receiving mail, which presents as sign-in mail that silently never arrives.
- **AUTH-12.1.2** For a signed callback, the signature is necessary and not sufficient. The
  implementation MUST also:
  - fetch the signing certificate only from a host it recognises, decided before the fetch, so
    that a payload cannot name the key it is to be checked against;
  - reject a certificate URL whose authority contains userinfo, because
    `https://sns.<region>.amazonaws.com@evil.example/` has `evil.example` for its host;
  - check that the message came from a topic the client expects. A valid signature establishes
    that the provider sent the message, not that the client's own topic did, and anyone with an
    account at that provider can point a topic of their own at somebody else's endpoint. This is
    the check that looks redundant and is not.
- **AUTH-12.1.3** Signature algorithms MUST be an allowlist, and SHA-1 MUST NOT be on it. Where a
  provider offers a stronger signature as a per-topic setting, refusing the weaker one costs the
  client a configuration change and is the correct trade.
- **AUTH-12.2** Suppression MUST be keyed per tenant, so that one tenant's bounce history is not
  observable through another tenant's behaviour.
- **AUTH-12.3** Sending to a hard-bounced or complained address MUST be refused, and the caller
  MUST receive a permanent `SendError`. What the person is then told is decided by the response
  policy (§14.2), not by the transport.
- **AUTH-12.4** Suppression MUST be clearable by the client, since addresses get fixed.
- **AUTH-12.5** Repeated bounces for an account's primary address SHOULD be reportable to the
  client; it is the single most common cause of "I cannot log in".

---

## 13. The authorisation boundary

The library owns identity. It owns nothing about permissions. This is a design requirement, not
a philosophical position, and it has consequences that must be built in rather than bolted on.

- **AUTH-13.1** The library MUST NOT store roles, permission flags, or an administrator marker
  of any kind. There is no `isAdmin`.
- **AUTH-13.2** Privileged operations (create or revoke an invitation, revoke another account's
  session, change a tenant's policy, clear suppression) are plain service functions with no
  permission check inside them. The client is responsible for calling them only when authorised.
  The optional HTTP integration target MUST therefore ship the sign-in routes and MUST NOT ship
  any administrative route, because it has no basis on which to authorise one.
- **AUTH-13.3** The client attaches its own roles through the invitation metadata payload of
  AUTH-8.7, which the library stores and returns without interpreting.
- **AUTH-13.4** Session validation returns identity and tenant only (AUTH-9.7). Permission
  resolution is entirely the client's.
- **AUTH-13.5** Account creation MUST be joinable to the client's own transaction, so that the
  client can create its role or profile records atomically with the account. This is provided by
  the optional `TransactionalStore` capability of AUTH-15.3, not by the base port: a crash
  between two separate transactions leaves an account nobody can act on, but requiring
  enlistment of every backend would tie the library to the client's database unconditionally.
- **AUTH-13.6** Account creation MUST signal whether the new account is the **first in its
  tenant**, so the client can assign its own owner role. With no roles in the library, nothing
  else makes a tenant's first account privileged, and every client would otherwise discover this
  when its first tenant turns out to have no administrator.
- **AUTH-13.7** The audit log's actor field is supplied by the caller and MUST be documented as
  unverified by the library. It records that the client said account X performed an action; it
  cannot record that X was entitled to.

---

## 14. Security requirements

### 14.1 General

- **AUTH-14.1.1** Rate limiting MUST be enforced on send requests and on code submissions,
  independently, at these scopes: per (tenant, address), **per address across all tenants**, per
  source IP, per tenant, and globally. The cross-tenant per-address limit is not optional:
  without it, an attacker spraying one address across many tenants multiplies the send budget by
  the tenant count and mail-bombs a third party through the library.
- **AUTH-14.1.2** Limiter state lives in shared storage (AUTH-3.4), behind its own port
  (AUTH-15.6).
- **AUTH-14.1.3** No credential, token, code, cookie value, or session identifier may be written
  to logs, traces, or error messages. Where correlation is needed, log a truncated digest.
- **AUTH-14.1.4** All state-changing endpoints MUST be CSRF protected. The magic link landing
  page in particular submits a `POST`, and that POST needs a token bound to the attempt cookie.
- **AUTH-14.1.5** Authentication pages MUST send `X-Frame-Options: DENY` or an equivalent CSP
  `frame-ancestors` directive.
- **AUTH-14.1.6** Secrets (pepper, cookie signing key, provider tokens, Apple signing key) MUST
  be supplied by configuration, never defaulted, and the design MUST permit rotation with an
  overlap window rather than a flag day.
- **AUTH-14.1.7** An append-only audit record MUST be written for: attempt created, link opened
  and on which side of the device boundary, code entered and outcome, session issued, session
  revoked, identity linked or unlinked, invitation created, sent, accepted, revoked, policy
  changed, consent granted or withdrawn, and any client-initiated action on an account.
- **AUTH-14.1.8** The library MUST expose a hook point for bot mitigation on the send endpoint
  (Turnstile, hCaptcha, or none), without depending on any particular provider.

### 14.2 Sign-in response policy

What a person is told when their address cannot sign in is a product decision that trades
account enumeration against usability. The library MUST NOT make it; it MUST make the safe
choice the default, and it MUST guarantee that whatever the client chooses cannot leak through a
channel the client did not intend.

- **AUTH-14.2.1** Beginning a sign-in MUST produce a structured outcome:

  ```
  inductive SignInOutcome
    | linkSent
    | unknownAddress
    | notInvited
    | domainNotAllowed
    | addressSuppressed
    | throttled
    | malformedAddress
  ```

- **AUTH-14.2.2** The response is chosen by a port:

  ```
  structure SignInResponse where
    message : SignInMessage        -- what the person is shown
    notice  : Option NoticeKind    -- an email to send in place of the link

  structure SignInResponsePolicy (m : Type → Type) where
    respond : TenantId → SignInOutcome → m SignInResponse
  ```

  `respond` receives the tenant, so a client can vary behaviour per tenant without the library
  needing a configuration knob for it.

- **AUTH-14.2.3** The default implementation MUST be **uniform silence**: every outcome maps to
  the same message and sends no notice. A client that configures nothing gets the
  enumeration-resistant behaviour. This default MUST be what the wiring produces without
  explicit opt-in, not merely what the documentation recommends.
- **AUTH-14.2.4 (critical)** The library MUST equalise the mechanical shape of the response
  regardless of outcome: identical HTTP status, identical header set, and response latency
  normalised to a fixed floor. Sending mail takes measurably longer than not sending it, so a
  policy choice would otherwise be undone by a timing oracle it never intended to open.
- **AUTH-14.2.4.1** "Identical header set" includes `Set-Cookie`. An outcome that begins no
  attempt has no attempt cookie to set, so the integration target MUST set one anyway, drawn the
  same way and of the same shape, or its absence reports the outcome the rest of the response was
  equalised to hide. A credential submitted against such a cookie MUST fail exactly as one
  submitted against an attempt that has expired.
- **AUTH-14.2.5** The policy MUST NOT be able to disable rate limiting, bypass suppression, or
  suppress audit logging. It chooses what is said, not what is done.
- **AUTH-14.2.6** The audit log and telemetry MUST always record the true outcome, whatever the
  person was told.
- **AUTH-14.2.7** The federated sign-in path MUST produce the same outcome type and go through
  the same policy, so that a client cannot accidentally make one path talkative and the other
  silent.
- **AUTH-14.2.8** Documentation MUST record the trade-off so a client can decide deliberately:
  policy-based rejections (`domainNotAllowed`, and the fact that a tenant is invitation-only)
  describe the tenant and leak nothing about individuals, so they are usually safe to state
  openly; membership-based rejections (`unknownAddress`, `notInvited`) identify people and are
  the part worth protecting. It should also record that rate limiting does more work here than
  wording does: a probe budget of a few per hour makes any oracle nearly worthless.

---

## 15. Storage

### 15.1 What is stored

Twelve kinds of record, every one of them tenant-scoped except the tenant configuration itself:

1. **Tenant auth config**: signup policy and allowlist, invitation-override flag, attempt and
   session lifetimes, enabled providers and their credentials, sending identity, base URL,
   `returnTo` allowlist, optional-classic-code and plus-tag flags.
2. **Account**: (tenant, normalised email) unique, plus the sending form of the address, status,
   timestamps.
3. **Verified additional emails**.
4. **Credentials**, modelled as an open set per AUTH-4.4.2, with (tenant, issuer, subject)
   unique for linked identities.
5. **Login attempt**: state, digests of the magic token, revealed code, optional emailed code,
   and binding nonce; the failed-attempt counter; expiry; requester IP and user agent.
6. **Invitation**: address, token digest, opaque metadata blob, state, expiry, actor,
   consumption time.
7. **Session**: identifier digest, account, timestamps, idle and absolute expiry, user agent,
   coarse location, revocation.
8. **OAuth state**: PKCE verifier, nonce, tenant, return target, expiry.
9. **Suppression list**, per AUTH-12.2.
10. **Rate limiter counters**, behind their own port per AUTH-15.6.
11. **Consent records**: account, subject, version, answer, and when, append-only per AUTH-4.6.3.
12. **Audit log**, append-only.

### 15.2 The port and its layering

- **AUTH-15.2.1** The public seam is a domain-level repository, `AuthStore`, expressed as a
  structure per AUTH-3.5. It exposes operations in the vocabulary of §4 to §12, never SQL, never
  a connection handle. A backend that is not a relational database MUST be implementable against
  it.
- **AUTH-15.2.2** The SQL backends MUST share one implementation, parameterised by a small
  dialect record:

  ```
  structure Dialect where
    placeholder    : Nat → String     -- "$1" or "?"
    upsert         : ...
    timestampCodec : ...
    ...

  def sqlAuthStore (d : Dialect) (conn : Connection) : AuthStore m
  ```

  Rationale: Postgres and SQLite agree on everything this workload needs (`INSERT ... ON
  CONFLICT`, `RETURNING`, partial indexes, transactions), and the differences are shallow.
  Writing the atomicity-critical statements once means reviewing them once. Two independent
  implementations would mean two independent chances to get compare-and-set wrong, which is
  precisely where a bug is a vulnerability.
- **AUTH-15.2.3** The core library MUST NOT depend on any driver. Each backend is a separate
  `lean_lib` target.

### 15.3 Transactions as an optional capability

- **AUTH-15.3.1** Enlistment in the client's transaction is a separate capability, not part of
  the base port:

  ```
  structure TransactionalStore (m : Type → Type) where
    store   : AuthStore m
    runInTx : {α : Type} → (AuthStore m → m α) → m α
  ```

- **AUTH-15.3.2** A backend supplying only `AuthStore` is valid, and serves clients that do not
  need atomic provisioning. A backend supplying `TransactionalStore` additionally satisfies
  AUTH-13.5.
- **AUTH-15.3.3** A client that needs AUTH-13.5 and chooses a backend without the capability
  MUST fail to compile, not fail at runtime.
- **AUTH-15.3.4** `runInTx` MUST be a scoped block rather than an exposed connection or
  transaction handle, so that non-SQL backends and the test backend can implement it.
- **AUTH-15.3.5** Documentation MUST state the consequence plainly: enlistment requires the
  library's tables to live in the client's own database, so a client using it cannot put
  authentication data elsewhere. That is the price of atomic provisioning, and clients who do
  not want it should not take the capability.

### 15.4 Contract

The port's contract is not its type signature. These are behavioural guarantees a backend can
typecheck while violating, and every one of them is load-bearing:

- **AUTH-15.4.1** Conditional consume is atomic and exactly-once under concurrent callers
  (AUTH-5.3.5).
- **AUTH-15.4.2** Uniqueness is enforced by the store, not checked by the caller: one account
  per (tenant, email), one identity per (tenant, issuer, subject), at most one live attempt per
  (tenant, address).
- **AUTH-15.4.3** Expiry is enforced on read. A sweeper is required to bound growth but
  correctness MUST NOT depend on it having run.
  - **AUTH-15.4.3.1** The port MUST expose the sweep, and it MUST remove only records that
    nothing can reach: attempts past their expiry, and sessions past their idle or absolute
    expiry or revoked. The audit log, consent records and delivery history are retention
    questions rather than expiry ones (AUTH-4.6.6, §18.5) and MUST NOT be swept.
  - **AUTH-15.4.3.2** The library MUST NOT schedule it. A client runs it from whatever it
    already uses for periodic work, and the cutoff is a parameter, because how far apart the
    clocks of the processes sharing that database are is not something this library can know.
- **AUTH-15.4.4** Tenant isolation holds for every operation (AUTH-4.2.4), and tenant deletion
  cascades with no orphans (AUTH-4.2.5).
- **AUTH-15.4.5** The audit log admits no update and no delete.
- **AUTH-15.4.6** A read following a write observes it. Session validation in particular MUST
  NOT be served by an asynchronous replica: a just-issued session failing its first validation
  is indistinguishable from a broken sign-in.

### 15.5 Conformance suite

- **AUTH-15.5.1** The library MUST ship a conformance test suite that any `AuthStore`
  implementation can be run against, covering every guarantee in §15.4 including the concurrent
  cases.
- **AUTH-15.5.2** Every shipped backend MUST pass it, and it MUST be runnable by third parties
  against their own backends. Without this, pluggable storage means every new backend is an
  unreviewed reimplementation of the security-critical parts.
- **AUTH-15.5.3** The suite MUST be what validates the dialect record of AUTH-15.2.2 as complete
  rather than Postgres-shaped.

### 15.6 The rate limiter is a separate port

- **AUTH-15.6.1** Rate limiting MUST NOT be part of `AuthStore`. Its access pattern is atomic
  increment-and-test within a sliding window, at a frequency and contention level unlike
  anything else the library stores.
- **AUTH-15.6.2** The port MUST be independently replaceable, so that a deployment can keep
  `AuthStore` on its primary database while pointing the limiter elsewhere.
- **AUTH-15.6.3** The reference implementation MAY share the `AuthStore` backend. Documentation
  MUST note the contention this creates on a single-writer backend (AUTH-15.8.3).

### 15.7 Schema and secrets

- **AUTH-15.7.1** Each backend owns its own schema and migrations. For Postgres, migrations MUST
  create objects in a dedicated schema (`auth`) so they cannot collide with the client's own,
  while remaining in the same database so that AUTH-15.3 is possible. SQLite has no schemas, so
  its objects carry an `auth_` prefix for the same purpose.

  Migrations MUST ship as SQL files, paired up and down, named in `leanmigrate`'s convention so
  that a client using it can adopt them into its own migration set unaltered. The library MUST NOT
  apply them, and MUST NOT record or verify that they were applied. Its bookkeeping would have to
  live somewhere, and `leanmigrate` writes to one `schema_migrations` table whose name is fixed and
  unqualified, so the only place available is the client's: two owners in one table break
  `rollback` for both, since each rolls back by id and neither has files for the other's. Keeping
  the library out of that entirely is a deliberate trade of a detectable failure for a much smaller
  design, and the cost of it MUST be documented (AUTH-15.7.5).
- **AUTH-15.7.2** Credential lookup is by digest, which works because HMAC is deterministic
  under a fixed pepper. Every stored digest MUST therefore carry the identifier of the key that
  produced it, and lookup MUST try the current key and any keys still within their overlap
  window. Without this, honouring AUTH-14.1.6 invalidates every outstanding session and
  invitation at the moment of rotation. This is part of the port contract, not a per-backend
  decision.
- **AUTH-15.7.3** Per-tenant provider credentials (Google client secrets, Apple `.p8` keys) are
  secrets at rest and MUST be either encrypted in the store or resolved through a secrets port
  supplied by the client. Globally configured secrets do not have this problem; per-tenant ones
  do.
- **AUTH-15.7.4** Timestamps MUST be stored as epoch integers, not a database-specific
  timestamp type. This removes a dialect difference rather than abstracting one, and matches the
  `Clock` port.
- **AUTH-15.7.5** Documentation MUST state that applying the migrations is the client's, and what
  happens when it is not done: a statement naming a column the database does not have, at the
  moment that statement first runs, rather than an error at startup.

### 15.8 Backends

- **AUTH-15.8.1** Postgres, via `leanpostgres`, is the reference backend and MUST supply the
  `TransactionalStore` capability.
- **AUTH-15.8.2** A SQLite backend MUST be built in the first version, not deferred. An
  abstraction with one implementation is not an abstraction, and any Postgres assumptions that
  leak into the port will not be visible until a second backend exists, by which point they are
  load-bearing.
- **AUTH-15.8.3** A SQLite deployment inherits constraints that MUST be documented rather than
  discovered:
  - **Single writer.** Concurrent code submissions serialise, which makes AUTH-5.3.5 trivially
    safe but requires WAL mode and a busy timeout or ordinary concurrency produces
    `SQLITE_BUSY`.
  - **Single process.** AUTH-3.4 requires any instance to serve any request in any flow, so a
    SQLite client is a single-process deployment. A shared filesystem is not a substitute.
  - **Limiter contention.** The counters are the hottest write path and contend with everything
    else on a single writer. See AUTH-15.6.2.

---

## 16. Testing

Follow the escalation in the project's `CLAUDE.md`: a proven theorem beats a property test,
which beats an example. Never leave `sorry`; the build treats warnings as errors, which is also
why the `plausible` tactic is unusable and properties must be written as explicit test runs.

- **AUTH-16.1** The following MUST be theorems, not tests. They are all finite case analysis or
  pure total functions over decidable structure, and a counterexample in any of them is a
  security defect rather than a cosmetic one:
  - Domain allowlist matching respects label boundaries: no domain whose match is a proper
    suffix without a label boundary is ever accepted (AUTH-7.3.1).
  - Domain matching is invariant under case and IDN normalisation.
  - Email parsing and normalisation are idempotent, and normalisation preserves the sending
    form of the local part.
  - The attempt state machine admits no transition into `completed` from `expired` or
    `abandoned`, and none from `pending` by code submission.
  - A completed attempt cannot complete again: `step` on a `completed` state yields an error for
    every event.
  - Consuming an invitation yields an account whose address and tenant are the invitation's, for
    every input.
  - The default response policy is constant: `respond t o₁ = respond t o₂` for all outcomes and
    all tenants. This is the formal statement of AUTH-14.2.3 and is provable by case analysis.
  - Base32 and base64url encode/decode round-trip. These are discharged by `leancrypto`, which
    carries them beside the definitions; nothing is owed here beyond depending on a version that
    has them.
- **AUTH-16.2** Tenant isolation SHOULD be enforced by types rather than tested (AUTH-4.2.4). If
  a type-level guarantee proves impractical, record why in a comment and rely on the conformance
  suite instead.
- **AUTH-16.3** Property tests are appropriate for: the rate limiter's monotonicity, template
  escaping, and canonicalisation of provider payloads. Where a property was chosen because a
  theorem would not close, record the obstacle in a comment.
- **AUTH-16.4** Examples are appropriate for: golden provider payloads, and rendered email
  templates.
- **AUTH-16.5** The full cross-device flow MUST be exercisable end to end with no network and no
  database server, using **SQLite in memory** as the test backend. There is no hand-written
  in-memory fake: the tests run the same statements production runs, which is what makes them
  evidence about the shipped code rather than about a parallel implementation. The cost, accepted
  deliberately, is that `lake test` requires the SQLite native dependency.
- **AUTH-16.6** Fakes MUST exist for the remaining ports: a capturing email transport, a
  settable clock, and a seeded deterministic random source.
- **AUTH-16.7** Tests MUST cover, at minimum, these adversarial cases: link opened cross-device
  does not issue a session; code accepted only with the matching attempt cookie; sixth wrong
  code abandons the attempt; expired attempt rejects a correct code; concurrent completion
  yields one session; invitation accept cannot be redirected to another address or tenant;
  federated identity with unverified email does not link; `returnTo` outside the allowlist is
  refused; an account in tenant A cannot be reached with a session from tenant B; the same
  address across many tenants hits the cross-tenant send limit.
- **AUTH-16.8** `lake build` and `lake test` MUST both pass, with no warnings, before any task
  is considered complete. Verify individual files with the Lean LSP diagnostics while working.

---

## 17. Code standards

Inherit the conventions in the project's `CLAUDE.md`, in particular:

- **AUTH-17.1** Every file starts with the copyright statement:
  `Copyright (c) 2026 Paul Butcher. All rights reserved.` and the Apache 2.0 notice.
- **AUTH-17.2** Comments explain *why*, never restate the code. No file or function header
  comments unless they add real value. No references to plans, milestones, or rejected designs.
- **AUTH-17.3** Never use an emdash. Use a comma or a semicolon.
- **AUTH-17.4** `partial` is forbidden unless genuinely unavoidable.
- **AUTH-17.5** If something would be better implemented as a change to a dependency, or is
  generally useful beyond this library, stop and ask rather than implementing it here.
- **AUTH-17.6** No git operations of any kind.

---

## 18. Open decisions

Unresolved unless the entry says otherwise. Each needs an answer before the affected part is
built; a recommendation is offered but the decision is not the implementer's to make. Ask, do not
assume. An entry that has been answered keeps its number and records what was decided.

- **18.1 Administrator-led recovery.** Self-service recovery is out of scope, so someone who
  loses mailbox access is restored by the client. The three operations that were named as
  probably necessary now exist for their own reasons: changing the primary address and
  force-revoking sessions came with §9, and resending an invitation with §8. What is still not
  specified is whether that is the whole of it, and in particular what an administrator is to do
  about an account whose mailbox is gone but whose new address is not yet proven; every path
  through §5 begins by mailing the address being claimed.

- **18.2 Per-tenant sending domains.** Deferred, and AUTH-10.2 keeps the retrofit cheap. What is
  not yet decided is whether tenants will eventually sign in at their own hostname as well as
  send from their own domain. AUTH-4.3.2 assumes not. If they will, the OAuth callback needs a
  shared origin plus a cross-origin handoff credential, which is a real piece of machinery worth
  knowing about before it is needed.

- **18.3 Passkeys.** Deferred, but they are the only phishing-resistant option and the likely
  next addition. Confirm that AUTH-4.4.2 is enough forward provision, or specify more.

- **18.4 Enterprise SSO.** SAML and SCIM are out of scope but are what B2B buyers ask for.
  Tenant-scoped accounts make a per-tenant identity provider a natural fit later; confirm
  nothing else is needed now.

- **18.5 Data protection.** Retention periods for audit records, attempts, and IP addresses;
  account deletion versus deactivation; data export.

- **18.6 Impersonation.** A client signing in as one of its accounts for support purposes is a
  common operational need and a serious security feature. In or out? If in, it needs its own
  audit trail and a visible indication to the person being impersonated.

- **18.7 Consent capture.** Answered, in §4.6: the library stores consent and does not capture
  it. The record, the version and the history are what could not be backfilled, and they now
  exist; the capture is the client's, on somebody it has already authenticated. Asking during
  sign-in was rejected because a consent control shown only to addresses with no account is a
  better account enumeration oracle than any channel §14.2 closes. What remains open is only what
  §18.5 decides: how long the records are kept, and what account deletion does to evidence that
  permission was given.

- **18.8 Localisation.** Are emails single-language? Locale selection has to be threaded from
  the request through to template rendering, which is easier to design in than to retrofit.

## 19. Suggested delivery order

Each stage should build, test, and be reviewable on its own.

1. Domain model, the pure state machine, and the theorems of AUTH-16.1. No IO.
2. The `AuthStore` port and its conformance suite, with the test backend passing it. The whole
   cross-device flow exercised with no server.
3. The shared SQL implementation and its dialect record, with both the Postgres and SQLite
   backends passing the conformance suite. Build both here; deferring the second defeats the
   abstraction.
4. Postmark outbound transport; the email flow working end to end.
5. Signup policies and invitations, including the metadata payload and the first-in-tenant
   signal.
6. The SES transport (AUTH-10.9), with both adapters satisfying one port.
7. Rate limiting, behind the port of AUTH-15.6 and at the five scopes of AUTH-14.1.1. It is
   listed as a stage because it was previously assigned to none, and so would have been
   delivered by nobody.
8. Session management surface, bounce ingestion, suppression.
9. Consent records (§4.6), which answer §18.7.

Federated sign-in was stage 6 and is deferred; see §6.
