# Known issues

Deliberate limitations of the current implementation, with the reasoning behind them. Each entry names the requirement it falls short of and what would close the gap.

## No committed test reaches a provider (§6, AUTH-16.5)

Federated sign-in is exercised against stubs, and the ID tokens in the suite are real ones signed by a real key. Google, Apple and GitHub have all be tested live in [TodoMVC Max](https://github.com/paulbutcher/lean-todomvc-max).

## Unlinking counts the magic link as a way in unless two conditions say otherwise (AUTH-6.8)

`Service.unlinkIdentity` counts the account's other credentials and the magic link to its primary address. Every account has a primary address, so the refusal fires only where that link is not available: where the tenant's `originPolicy` does not admit `emailAddress` at all, or where mail to the address has been suppressed. Both are real conditions and both are tested, but a deployment on the defaults, expecting to be stopped from unlinking a sole provider identity or a sole passkey, will not be.

That is the honest shape of AUTH-6.8 rather than a shortfall against it: on a tenant that admits the magic link, the address really is a way in, and refusing the unlink would be refusing on a hazard that does not exist. What a deployment wanting the stricter rule does is set the origin policy, which is also what makes a passkey the floor of an account's security rather than its ceiling.

## An invitation names one provider, and a tenant may have several (AUTH-8.6)

Where `originPolicy` does not admit the magic link, the invitation mail points at the federated start of the first provider in `TenantConfig.providers`, carrying the invitation. That is the whole of the choice the library makes, and on a tenant offering two providers it makes it for the invited person: the mail names one, and the others are reachable only from a page the application wrote.

The order is the tenant's own rather than arbitrary, which is what makes picking the first defensible. It is still a choice nobody asked to be made, and a tenant enforcing SSO through two providers, one per acquired company say, will mail half its invitations to the wrong sign-in.

Closing it needs a page offering the choice, and that page is not this library's to serve: AUTH-22.19 and the project's rule against JavaScript both land on the same line, that the markup around a sign-in belongs to the application that knows what its sign-in looks like. What would close it here is `Service.invitationLink` taking the provider rather than choosing one, so a client sending its own invitation mail names the provider it means. That is a small change and nothing has asked for it.

## The emailAddress credential has no writer (AUTH-4.4.2)

`Credential.descriptor` has an `emailAddress` variant and nothing creates one. The magic link route identifies an account by its primary address rather than by a credential row, so the variant is forward provision rather than something in use. The federated and passkey routes both write their own rows, so the set is not empty, only narrower than the type allows.

Passkeys arriving did not change this, which is worth saying because it was expected to. A passkey is found by the handle on its descriptor, and a magic link is still found by the account's address, so the kind that would need an `emailAddress` row is one that proves an address by some means the library does not yet have.

## The authenticator the ceremony met is a virtual one (§18.3, AUTH-16.5)

`test/fixtures/passkey-capture.json` is a whole ceremony, registration and assertion from one credential, produced by Chrome's virtual authenticator over the DevTools protocol and committed by `make-passkey-capture.mjs`. The key the assertion verifies against is read out of its own registration, so nothing in that loop was laid out, keyed or signed by this repository. That was the gap, and it is closed.

What remains is narrower. Chrome's virtual authenticator is Chrome's own CTAP2 implementation, not silicon: it is independent of this library, which is the property the fixture was for, but it is one implementation and a popular one. A security key, a phone and a TPM each sign the same structures and differ in what they put in the fields around them, which is why the py_webauthn capture is kept beside it: that one is from a real device, and between them the layout is confirmed twice over by code this repository did not write.

The relying party is `localhost` and the origin carries a port, because WebAuthn treats localhost as a secure origin without a certificate. A deployment runs on neither, so what the fixture cannot exercise is an origin check against a real host, which is a string comparison the other fixtures do cover.

Regenerating it needs Node, Playwright and its Chromium, which no part of the build or the suite requires: the script is run by hand and the JSON is what the suite reads, because AUTH-16.5 forbids a committed test from reaching anything.

## No committed test makes an HTTP request (AUTH-16.5)

`Authentication.Postmark.curlHttp` and `Authentication.Ses.curlHttp` are the only parts of the outbound transports the suite never runs. Everything above it is covered: the payload built, the responses interpreted, and the flow from `begin` through the template into the request. What is not covered is leancurl itself, and so whether the payload leaves this process intact.

This is deliberate. AUTH-16.5 requires the flow to be exercisable with no network, and a suite that reaches an external service fails when that service has a bad day rather than when this library does.

It was verified once by hand, against Postmark's `POSTMARK_API_TEST` token, which validates a payload without sending it and needs no account. That confirmed the field names, that `MessageStream` and `Metadata` are accepted, and that the response shape is what the golden payload in `test/Tests/Postmark.lean` says; the payload there is that capture rather than a transcription. Repeating it means writing a few lines against `curlHttp` with that token as the server token. Anyone changing the request should.

The residue is that a change to how leancurl is called would pass the suite and fail in production. The metadata length check in `test/Tests/Postmark.lean` guards the one case where that would otherwise be silent.

The webhook parsers have the same standing as the payloads they were written against, which is documentation rather than capture. Postmark's bounce and spam-complaint bodies and the SES notifications inside their SNS envelope are transcribed from the providers' published examples, so a field either provider has since renamed would pass the suite and drop every bounce in production, silently: an address that should have been suppressed simply is not. The first live bounce is the test, and it is worth watching for.

The SNS *signature* is in better standing than the payloads it covers. `test/fixtures/` holds a real key, a real certificate, and messages signed by `openssl` over an independently built canonical string, so the verifier is checked against bytes this repository cannot produce. What those fixtures cannot establish is that AWS builds the canonical string the same way: they were signed over this library's reading of the specification, so a misreading would be consistent across both. A signature from AWS itself is the only thing that settles that, and the first live notification is it.

The SES adapter has never been run against SES at all, not even by hand, so its standing is weaker again: the request it builds is checked against what SigV4 says a signed request should look like, and `leanaws` is checked against AWS's published cases, but no signature this adapter produced has ever been offered to AWS. The first live send is the test.

## Migrations are shipped but not applied or tracked (AUTH-15.7.1)

Each backend ships its schema as up and down SQL under `migrations/`, named in `leanmigrate`'s convention so a client using it can adopt the files unaltered. What the library does not do is run them, or record that they ran, or check at startup that they did.

The consequence is the one that prompted all this. A client who takes a new version and does not apply its migration has a database missing a column, and finds out when a statement first names that column rather than when the process starts. That is exactly how the gap was found the first time: adding `attempts.invitation_id` passed against a fresh SQLite database and failed against a Postgres database an earlier stage had created.

Closing it properly needs bookkeeping the library can call its own, and there is nowhere to put it. `leanmigrate` writes to a single `schema_migrations` table whose name is fixed in its engine and unqualified, so on SQLite it is shared by construction and on Postgres it resolves through `search_path` into the client's schema. Two owners in one table leave `migrateUp` and `pending` working, because each filters the ids on disk against the table, but they break `rollback` in both directions: it selects ids from the table alone, then fails with `cannot roll back <id>: no migration files found for it` on the first id belonging to the other owner. A shared 14-digit timestamp id would collide on the primary key as well, failing a migration for a reason nobody would guess from the message.

What would close it is a configurable bookkeeping table in `leanmigrate` plus a startup check comparing the ids this library ships against the ones recorded. That was weighed and judged more machinery than the problem justifies while a loud, if late, failure is the alternative. It should be revisited if the schema starts changing often enough that clients fall behind in practice.

## The response is equalised only for a client that uses the shipped routes (AUTH-14.2.4)

`AuthenticationHttp` answers every outcome of a sign-in request with the same status, the same headers and one `Set-Cookie`, and `begin` already equalised the time. A client that mounts those routes has AUTH-14.2.4.

A client that wires its own routes against the service does not, and nothing here would notice: it can answer one outcome with a 200 and another with a 404, or set a cookie on the outcomes that made an attempt and not on the ones that did not. `TenantConfig.returnTo` (AUTH-9.8) is offered the same way. The service returns what a correct response needs and cannot make anything use it.

That is inherent rather than pending. The alternative is a library that owns the response, which would mean owning the framework, and AUTH-2.2 rules that out for good reasons of its own.

The floor is also only on `begin`. A code submission takes a different amount of time against a live attempt than against one that has expired, which is a smaller oracle against a much smaller budget, but it is one.

## Bot mitigation is a port with no implementation (AUTH-14.1.8)

`HumanCheck` is asked on the send endpoint before anything else happens, and the default implementation admits everyone. That is the honest default: a library that shipped a check would be shipping a provider, and AUTH-2.4 says such a choice is not this library's to make.

A deployment that configures nothing has not met AUTH-14.1.8. What stands between it and a flood is the rate limiter, which is real but blunt: the limits of AUTH-14.1.1 bound how much mail a flood produces, not how much traffic reaches the endpoint.

Closing it is a client writing about ten lines against whichever provider it uses: the answer arrives in a form field the route is told the name of, and the port hands it to the client's `verify`. Nothing in the library needs to change.

## The SNS signing certificate is fetched on every message (AUTH-12.1.1)

`Ses.curlSubscription` fetches the certificate a notification names each time one arrives. SNS rotates that certificate rarely and names the same URL on every message, so a busy endpoint makes one outbound request per bounce for a document that almost never changes.

That is deliberate. A cache belongs to the deployment: it needs an eviction policy, and a wrong one is worse than none, because a certificate cached past a rotation rejects everything and a cache keyed carelessly accepts the wrong key. `Subscription.certificate` is a function, so a client that wants caching wraps it with one whose behaviour it can see, rather than finding one here it cannot.

The consequence while it stands is latency and outbound traffic on the ingestion path, not correctness. It matters at a volume of bounces that would already be an incident.

## Sweeping is offered but never runs by itself (AUTH-15.4.3.2)

`Service.purgeExpired` removes the attempts and sessions nothing can reach, and the library never calls it. A client that mounts the routes and schedules nothing has a database that grows for as long as it runs.

That is deliberate for the reason AUTH-15.4.3.2 gives: the cutoff depends on how far apart the clocks of the processes sharing that database are, and a library that swept on its own timer would be choosing that, on a schedule the client cannot see, against a database the client owns.

Correctness never depends on it. Everything the sweep removes is already refused on read, so the consequence of never running it is disk and index size, not a session that should have ended still answering. It is listed here because the failure is silent and slow: nothing degrades until the attempts table is large enough for its own index to matter.

The authorisation server has a sweep of its own, `OAuth.Service.purgeExpired`, and the same is true of it. So does `OAuth.Service.pruneClients`, and there the growth is faster: some clients register once per fresh connection, so the registrations table grows with connections rather than with people.

## Client-initiated sends are not rate limited (AUTH-14.1.1)

The limiter covers beginning a sign-in and submitting a code. Creating and resending an invitation send mail too, and are not counted.

That is deliberate rather than overlooked: both are privileged operations the client calls only when it has decided who may call them (AUTH-13.2), so they are not reachable by whoever is knocking on the sign-in page. It stops being true the moment a client exposes resend to an unauthenticated route, which is the failure worth naming here because nothing in the types will prevent it.

`Service.createRecovery` is in the same position and is the one to watch, because what it returns is a bearer token standing in for a session on an account that already exists. It is unlimited for the same reason and stops being safe under the same mistake.

## The ceremony routes are not rate limited (AUTH-14.1.1)

`beginFederated` counts a start against the limiter; the passkey and recovery ceremonies do not. Beginning a passkey authentication writes a ceremony row for anyone who asks, with no session and nothing to identify them by, so a client mounting those routes has an unauthenticated way to make a server write rows as fast as it can be asked.

Recovery is the tighter of the two rather than another instance of it. The enrolment routes read a grant and write nothing until the grant and its token are both good, so what a flood of invalid tokens costs is a lookup each; and the token is 128 bits, so it is not a credential anybody guesses. Correctness does not depend on any of this, and the sweep removes what accumulates (AUTH-15.4.3).

Closing it is the limiter the library already has, with an action per ceremony and the scopes `beginFederated` uses. It was not done when the passkey routes landed, and recovery inherited the gap rather than widening it.


## The client metadata document fetcher is a port with no implementation (AUTH-20.2.2)

Resolving a `client_id` that is a URL means fetching that URL, and outbound HTTP is not something this library does. `ClientDocuments` is the seam and no adapter ships behind it, so a deployment that wants client ID metadata documents writes one.

What the adapter owes is not only the request. It must refuse any scheme but `https`, must not follow a redirect to a host the identifier check would have refused, must apply a timeout, and must report the body's size and whatever freshness the response's cache headers allowed (AUTH-20.2.3, AUTH-20.2.4). The identifier check above the seam refuses literal private and loopback addresses, and that is a floor rather than a substitute: a name that resolves to one passes it, and only the adapter is in a position to notice.

A deployment that supplies no adapter is not broken, and it is no longer silently narrower than its metadata document says. `documents` is absent, the document reports that, and a client reads it and registers dynamically instead. One that asks anyway is refused with `invalid_client` and told that URL client identifiers are not accepted here, rather than that a fetch failed.

## The authorisation server records no audit events of its own (AUTH-20.17.10)

Granting and withdrawing a grant are consent records, so they reach the audit log through §4.6 exactly as any other consent does. Nothing else does: which client redeemed which code, when a token was issued, and when a replayed refresh token revoked a grant are not in the log.

The reason is where `AuditEvent` lives. It is a closed inductive in the core target, and every case of it is decoded by `auditColumns` in the shared SQL store, which a consumer taking only magic links links today. Naming the authorisation server's events there is a change to the core library rather than to this target, and AUTH-20.18.1 records it as a decision rather than making it quietly. The linking events of AUTH-14.1.7 have since been added there, so the cost is one already paid rather than an untouched one; what has not changed is that nothing requires these.

## A rotated pepper must stay in the ring for the session lifetime (AUTH-15.7.2)

A session digest is written once, when the session is issued, and never written again: `touchSession` slides the idle timeout and records the last use, and touches no digest. The pepper that minted a session therefore has to stay in `PepperRing.retired` until every session minted under it has expired, which `sessionAbsoluteLifetime` puts at 90 days by default. Rotating twice inside that window, or dropping a retired pepper early, signs everybody holding an older session out.

Refresh tokens do not have this problem, because rotation on use re-digests them under the current pepper, so they leave a retired one behind within a refresh interval. Giving sessions the same property means re-digesting the presented credential at touch time, which is a change to the store port rather than to the service, and it buys a shorter window at the cost of a write on every request.

## The authorisation server's endpoints are not rate limited (AUTH-20.18.2)

The limiter of §15.6 covers beginning a sign-in and submitting a code. Nothing counts authorization requests, token requests, or registrations.

Registration is the one worth naming. It is unauthenticated by design, it writes a row, and AUTH-20.6.7 bounds what accumulates rather than what arrives; a deployment that exposes it without a limiter in front of it has a way to make a server write rows for nothing.

## The shipped routes do not report an account's creation (AUTH-13.6, AUTH-8.7)

`Service.Outcome.admitted` says that an account was created, whether it was the first in its tenant, and what metadata the invitation it accepted carried. A client driving `Service` itself reads it there. None of the shipped route sets passes it on: `Http.Config`, `OidcHttp.Config` and `PasskeyHttp.Config` have no hook for it, so a client mounting them never learns that the account it is now looking at is new, and has no signal for making a tenant's first account its owner.

The invitation metadata can be recovered afterwards, by finding the accepted invitation whose address is the account's, and `docs/invitations.md` shows how. The first-in-tenant signal cannot, because nothing records it. Closing this needs a callback on each route config, defaulting to doing nothing, which is an addition to three public structures.

## A tenant admitting only passkeys takes no new members (AUTH-8.11)

A passkey resolves to an account and never creates one, and `.only [.passkey]` refuses the magic link and every provider, so nothing can create an account. Invitations are refused with `noWayToAccept` for that reason, and the library has no operation that creates an account outside a sign-in.

Existing accounts are unaffected, and a recovery grant still enrols a new passkey onto one. A tenant that needs to grow admits a provider beside passkeys. Provisioning an account by administrator action, followed by a recovery grant to enrol its first passkey, would close it; nothing has asked for that.
