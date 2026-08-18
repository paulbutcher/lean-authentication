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

## The response is equalised in time but not in shape (AUTH-14.2.4)

Beginning a sign-in now leaves through a configurable floor, so the outcome that sent mail and the
outcome that did nothing take the same time to answer. That closes the half of AUTH-14.2.4 this
library can close on its own.

The other half, an identical HTTP status and an identical header set whatever the outcome, belongs
to the layer that turns an `Outcome` into a response, and that layer does not exist yet: the
optional HTTP integration target of AUTH-13.2 is not built. A client wiring its own routes today
can undo the response policy by answering one outcome with a 200 and another with a 404, and
nothing here would notice.

The same absence leaves two other things offered rather than enforced. `TenantConfig.returnTo`
validates a redirect target against the tenant's allowlist (AUTH-9.8), and the session cookie
arrives in `Outcome.setCookies` with the attributes AUTH-9.2 fixes, but nothing makes a client
call the first or set the second. Both are the shape they are so that using them is easier than
not, which is as far as a library with no route layer can go.

The floor is also only on `begin`. A code submission takes a different amount of time against a
live attempt than against one that has expired, which is a smaller oracle against a much smaller
budget, but it is one.

## Delivery events are parsed but not authenticated (AUTH-12.1.1)

`Postmark.deliveryEvents` and `Ses.deliveryEvents` read a payload. Neither establishes that the
payload came from the provider, and `Service.ingestDelivery` trusts what it is handed.

That is placement rather than oversight, and the requirement says so: the credential that would
answer the question belongs to the route. Postmark authenticates its webhooks with HTTP basic
auth on a URL the client chose, which this library never sees. SNS signs each post with a
certificate the receiver fetches from a URL in the message and validates against the signing
key, and it also posts a `SubscriptionConfirmation` that has to be answered before any
notification arrives at all. Neither is reachable from a function that is given a string.

The consequence is worth stating plainly because it is the whole of the exposure: an endpoint
that forwards its body to `ingestDelivery` without checking is one by which anyone who finds the
URL can suppress any address in that tenant, which is a denial of sign-in that looks like mail
that simply never arrives. `README.md` says so where a client wiring the endpoint will read it,
and the module comments say so where a client reading the parser will.

What would close it is the HTTP integration target of AUTH-13.2 shipping the two endpoints with
their verification, at which point the client would have nothing to skip.

## Client-initiated sends are not rate limited (AUTH-14.1.1)

The limiter covers beginning a sign-in and submitting a code. Creating and resending an invitation
send mail too, and are not counted.

That is deliberate rather than overlooked: both are privileged operations the client calls only
when it has decided who may call them (AUTH-13.2), so they are not reachable by whoever is
knocking on the sign-in page. It stops being true the moment a client exposes resend to an
unauthenticated route, which is the failure worth naming here because nothing in the types will
prevent it.

