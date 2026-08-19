# Known issues

Deliberate limitations of the current implementation, with the reasoning behind them.
Each entry names the requirement it falls short of and what would close the gap.

## Internationalised domain names are not accepted (AUTH-4.5.2)

`Domain.parse` accepts ASCII domains only. A domain containing non-ASCII characters (a
U-label, for example `münchen.de`) is rejected with a distinct error rather than being
converted to punycode. Already-encoded A-labels (`xn--mnchen-3ya.de`) are ordinary ASCII
and are accepted, so an address whose domain has been punycoded upstream works today.

AUTH-4.5.2 requires the conversion to happen in the library, so that two addresses
differing only in IDN encoding are the same address. Until an encoder exists, they are
instead one address and one rejection: no address is silently mapped to the wrong account,
which is the failure that would matter.

The reason for the limitation is placement, not difficulty. RFC 3492 punycode is
general-purpose code with no connection to authentication, and AUTH-2.4 and AUTH-17.5 both
require that such code be surveyed against the ecosystem and, where it does not exist,
raised as a question about which library should own it rather than written here. The survey
found no punycode implementation for Lean 4, and the decision on where it belongs is
outstanding.

Consequences while it stands:

- A tenant whose people have non-ASCII email domains cannot use the library.
- The AUTH-16.1 theorem that domain matching is invariant under IDN normalisation holds
  only over the ASCII domains the parser accepts, which makes it a weaker statement than
  the requirement intends.

Closing it is a drop-in: an encoder applied per label in `Domain.parseFolded`, between the
split on separators and the character check that currently rejects the label. Nothing
downstream of the parser needs to change, because everything downstream already works on
normalised labels.

## No committed test makes an HTTP request (AUTH-16.5)

`Authentication.Postmark.curlHttp` and `Authentication.Ses.curlHttp` are the only parts of the
outbound transports the suite never runs. Everything above it is covered: the payload built, the responses interpreted, and the flow
from `begin` through the template into the request. What is not covered is leancurl itself, and
so whether the payload leaves this process intact.

This is deliberate. AUTH-16.5 requires the flow to be exercisable with no network, and a suite
that reaches an external service fails when that service has a bad day rather than when this
library does.

It was verified once by hand, against Postmark's `POSTMARK_API_TEST` token, which validates a
payload without sending it and needs no account. That confirmed the field names, that
`MessageStream` and `Metadata` are accepted, and that the response shape is what the golden
payload in `test/Tests/Postmark.lean` says; the payload there is that capture rather than a
transcription. Repeating it means writing a few lines against `curlHttp` with that token as the
server token. Anyone changing the request should.

The residue is that a change to how leancurl is called would pass the suite and fail in
production. The metadata length check in `test/Tests/Postmark.lean` guards the one case where
that would otherwise be silent.

The webhook parsers have the same standing as the payloads they were written against, which is
documentation rather than capture. Postmark's bounce and spam-complaint bodies and the SES
notifications inside their SNS envelope are transcribed from the providers' published examples,
so a field either provider has since renamed would pass the suite and drop every bounce in
production, silently: an address that should have been suppressed simply is not. The first live
bounce is the test, and it is worth watching for.

The SNS *signature* is in better standing than the payloads it covers. `test/fixtures/` holds a
real key, a real certificate, and messages signed by `openssl` over an independently built
canonical string, so the verifier is checked against bytes this repository cannot produce. What
those fixtures cannot establish is that AWS builds the canonical string the same way: they were
signed over this library's reading of the specification, so a misreading would be consistent
across both. A signature from AWS itself is the only thing that settles that, and the first live
notification is it.

The SES adapter has never been run against SES at all, not even by hand, so its standing is weaker
again: the request it builds is checked against what SigV4 says a signed request should look like,
and `leanaws` is checked against AWS's published cases, but no signature this adapter produced has
ever been offered to AWS. The first live send is the test.

## Migrations are shipped but not applied or tracked (AUTH-15.7.1)

Each backend ships its schema as up and down SQL under `migrations/`, named in `leanmigrate`'s
convention so a client using it can adopt the files unaltered. What the library does not do is run
them, or record that they ran, or check at startup that they did.

The consequence is the one that prompted all this. A client who takes a new version and does not
apply its migration has a database missing a column, and finds out when a statement first names
that column rather than when the process starts. That is exactly how the gap was found the first
time: adding `attempts.invitation_id` passed against a fresh SQLite database and failed against a
Postgres database an earlier stage had created.

Closing it properly needs bookkeeping the library can call its own, and there is nowhere to put it.
`leanmigrate` writes to a single `schema_migrations` table whose name is fixed in its engine and
unqualified, so on SQLite it is shared by construction and on Postgres it resolves through
`search_path` into the client's schema. Two owners in one table leave `migrateUp` and `pending`
working, because each filters the ids on disk against the table, but they break `rollback` in both
directions: it selects ids from the table alone, then fails with `cannot roll back <id>: no
migration files found for it` on the first id belonging to the other owner. A shared 14-digit
timestamp id would collide on the primary key as well, failing a migration for a reason nobody
would guess from the message.

What would close it is a configurable bookkeeping table in `leanmigrate` plus a startup check
comparing the ids this library ships against the ones recorded. That was weighed and judged more
machinery than the problem justifies while a loud, if late, failure is the alternative. It should
be revisited if the schema starts changing often enough that clients fall behind in practice.

## The response is equalised only for a client that uses the shipped routes (AUTH-14.2.4)

`AuthenticationHttp` answers every outcome of a sign-in request with the same status, the same
headers and one `Set-Cookie`, and `begin` already equalised the time. A client that mounts those
routes has AUTH-14.2.4.

A client that wires its own routes against the service does not, and nothing here would notice:
it can answer one outcome with a 200 and another with a 404, or set a cookie on the outcomes that
made an attempt and not on the ones that did not. `TenantConfig.returnTo` (AUTH-9.8) is offered
the same way. The service returns what a correct response needs and cannot make anything use it.

That is inherent rather than pending. The alternative is a library that owns the response, which
would mean owning the framework, and AUTH-2.2 rules that out for good reasons of its own.

The floor is also only on `begin`. A code submission takes a different amount of time against a
live attempt than against one that has expired, which is a smaller oracle against a much smaller
budget, but it is one.

## Bot mitigation is a port with no implementation (AUTH-14.1.8)

`HumanCheck` is asked on the send endpoint before anything else happens, and the default
implementation admits everyone. That is the honest default: a library that shipped a check would
be shipping a provider, and AUTH-2.4 says such a choice is not this library's to make.

A deployment that configures nothing has not met AUTH-14.1.8. What stands between it and a flood
is the rate limiter, which is real but blunt: the limits of AUTH-14.1.1 bound how much mail a
flood produces, not how much traffic reaches the endpoint.

Closing it is a client writing about ten lines against whichever provider it uses: the answer
arrives in a form field the route is told the name of, and the port hands it to the client's
`verify`. Nothing in the library needs to change.

## The SNS signing certificate is fetched on every message (AUTH-12.1.1)

`Ses.curlSubscription` fetches the certificate a notification names each time one arrives. SNS
rotates that certificate rarely and names the same URL on every message, so a busy endpoint makes
one outbound request per bounce for a document that almost never changes.

That is deliberate. A cache belongs to the deployment: it needs an eviction policy, and a wrong
one is worse than none, because a certificate cached past a rotation rejects everything and a
cache keyed carelessly accepts the wrong key. `Subscription.certificate` is a function, so a
client that wants caching wraps it with one whose behaviour it can see, rather than finding one
here it cannot.

The consequence while it stands is latency and outbound traffic on the ingestion path, not
correctness. It matters at a volume of bounces that would already be an incident.

## Client-initiated sends are not rate limited (AUTH-14.1.1)

The limiter covers beginning a sign-in and submitting a code. Creating and resending an invitation
send mail too, and are not counted.

That is deliberate rather than overlooked: both are privileged operations the client calls only
when it has decided who may call them (AUTH-13.2), so they are not reachable by whoever is
knocking on the sign-in page. It stops being true the moment a client exposes resend to an
unauthenticated route, which is the failure worth naming here because nothing in the types will
prevent it.

