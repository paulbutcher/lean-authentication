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

The SES adapter has never been run against SES at all, not even by hand, so its standing is weaker
again: the request it builds is checked against what SigV4 says a signed request should look like,
and `leanaws` is checked against AWS's published cases, but no signature this adapter produced has
ever been offered to AWS. The first live send is the test.

## Neither backend has migrations (AUTH-15.7.1)

Each backend ships a `createSchemaSql` that is a `CREATE TABLE IF NOT EXISTS` script run at
startup. It creates; it does not migrate. `IF NOT EXISTS` does nothing to a table that already
exists, so a column added in a later release is silently absent from every database created
before it, and the failure appears when a statement first names the column rather than when the
schema is applied. Neither backend records which version of the schema it is at, so nothing can
detect the mismatch either.

This was found the way it will always be found: adding `attempts.invitation_id` passed against a
fresh SQLite database and failed against a Postgres database an earlier stage had created.

The current answer is that the schema has no deployments to preserve, so a change to it means
recreating the database. That answer expires at the first release.

AUTH-15.7.1 requires Postgres migrations to ship with the backend via `leanmigrate`, which exists
(`paulbutcher/leanmigrate`, `v0.3.1`) and was not adopted in stage 3. It should be adopted before
a schema change has to preserve anything. The SES transport touches no schema, so the reprieve
lasts exactly one stage: rate limiting adds counters, and a suppression list follows.

## Rate limiting is not enforced (AUTH-14.1.1)

Nothing limits how often a sign-in may be begun, and there is no `RateLimiter` port yet.
AUTH-14.1.1 requires limits at five scopes, and the cross-tenant per-address limit in
particular is what stops an attacker spraying one address across many tenants and mail-bombing
a third party through the library.

This is not a deferred stage: the delivery order in REQUIREMENTS §19 does not assign rate
limiting to any stage, so it would otherwise be delivered by nobody. It needs its own port per
AUTH-15.6, and it should land before anything is deployed, because AUTH-14.2.8 records that
rate limiting does more work than wording does in protecting against enumeration.
