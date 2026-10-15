# Passkey plan

The work to add WebAuthn passkeys: the decisions it rests on, the order to take it in, and what it breaks. The decisions are taken and Track A has shipped; nothing else is built. One of those decisions, the user handle, cannot be revisited once a credential exists.

## Decisions

| Question | Answer |
| --- | --- |
| Where CBOR lives | A new `lean-cbor` package, decode and encode, not a module here |
| Pages or JSON | JSON ceremony endpoints and no pages, so the library ships no JavaScript |
| Attestation | Accept `none`, treat the rest as self-attestation, verify no statement |
| Credential discoverability | Discoverable only |
| User handle | An opaque random value per (tenant, account), minted at first registration |
| Sign counter | Stored, a regression audited, never revoked on |

CBOR belongs outside this repo because it is useful to anything speaking COSE, CTAP or WebAuthn, and it is where the proof content is. Serving no pages keeps the UI rule intact: `navigator.credentials` is script-only, and the twenty lines of glue belong to the application, as the authorisation server's rendering already does. Full attestation verification needs the FIDO metadata service, which AUTH-16.5 forbids any committed test from reaching.

Discoverable-only is load-bearing rather than a preference. The alternative sends `allowCredentials` for a named address, which is an account enumeration oracle in a library whose headline guarantee is that every sign-in outcome says the same thing. Discoverable credentials mean authentication never takes an address, so there is nothing to enumerate.

The user handle is the one irreversible decision. It is written into every authenticator that registers and cannot change afterwards without invalidating all of them. It is opaque and per tenant because an RP ID is a registrable domain while every identifier here carries a tenant, and the address must not be used: the handle is stored on the authenticator in clear and shown in account pickers.

## Track A: lean-cbor, done

Published as `lean-cbor` at `v0.1.0`, pinned here at `3ed60c3`, and required in the lakefile ahead of the target that will import it. It has no dependencies of its own, so it adds nothing to the graph a consumer resolves.

It covers the CTAP2 canonical subset: major types 0 through 5 and 7, definite length only, no tags. Indefinite lengths, non-canonical map ordering, duplicate keys, non-minimal heads and trailing bytes are all refused, each naming its reason and the byte offset where it was found. There is one decode and it enforces canonical order as it reads. `decodePrefix` reports where an item ends, which is how the credential public key is found inside `authenticatorData`.

The round trip and canonical uniqueness are proved, along with the prefix decode, and with the lemmas showing that neither the distinct-keys nor the depth hypothesis is vacuous. The proofs rest on nothing beyond `propext`, `Classical.choice` and `Quot.sound`.

Two things differ from what was specified for it, both deliberate and neither affecting this work. Map keys are restricted to integers and text strings, which is what makes detecting a duplicate by comparing encodings sound, and covers every key COSE and WebAuthn use. The depth bound is fixed at 1024 rather than raisable, because encoding, decoding and comparison all recurse on the stack.

## Track B: the credential origin policy

A tenant-level statement of which credential kinds may originate a session, as distinct from which kinds exist on an account. Independent of every phase below and a fraction of their size.

It is what makes passkeys worth the decoder. Without it the magic link remains available on every account, so an account's strength stays that of its mailbox and passkeys raise the ceiling rather than the floor. It also unblocks enforced SSO, and gives `RevocationReason.recovery` its first producer: nothing currently constructs it, so AUTH-9.6's requirement to revoke on "any recovery action" has no implementation.

Not a blocker for the mechanism, so it may land before, after or alongside. Before is better, because three features want it.

## Phase 1: the pure domain

Follow the federation precedent. `Authentication/Federation.lean` holds the state record and the pure decision while `AuthenticationOidc` holds the protocol, and that split is why the SQL store implements federation without linking OpenSSL.

A new `Authentication/Passkey.lean` holds four things. `PasskeyCeremony` mirrors `FederationState`: expiry enforced on read, single use, compare-and-set on commit. `PasskeyRegistration` holds the stored attributes, being the public key, COSE algorithm, sign count, transports, AAGUID, the backup eligible and backup state flags, and a client-supplied label. `PasskeyAssertion` is what an authenticator said once its signature has been checked. `Passkey.decide` is the analogue of `Federation.decide`: pure, writes nothing, decides sign-in against a looked-up credential.

`PasskeyId` belongs here too, and is not indexed by a tenant, for the reason `FederatedIdentity` is not: it names a credential at the authenticator, which knows nothing of tenants.

The user handle is the account's own identifier rather than a second value stored beside it. `AccountId` is already opaque, random per account and never the address, which is everything a handle has to be; and since a handle cannot be changed once an authenticator holds it, a separate one would be a value obliged to agree with the account forever.

One difference from `FederationState` needs saying in its doc comment, because it reads as an inconsistency otherwise. That record holds its verifier and nonce in clear because both must be given back to the provider. A passkey challenge is only ever compared, since the browser echoes it in `clientDataJSON`, so it is held as a `Digest` like every other credential here. The ceremony record is strictly more conservative than the federation one.

The cookie mirrors `Attempt.cookieValue`: the ceremony id plus a binding nonce, so that holding the id is not enough to be taken for the browser that started the ceremony.

## Phase 2: store, schema, conformance

`CredentialDescriptor.passkey` lands here rather than in Phase 1, with its `kind` and `origin` cases. It cannot be added before the store, because the SQL table fans each descriptor variant out to its own columns and adding a variant stops five of those mappings compiling. A variant with nowhere to put its identifier is worse than no variant at all.

`AuthStore` gains operations to create, read and compare-and-set a ceremony, to find a credential by passkey id, to read and update the registration attributes, and a purge case.

The schema adds one `credential_id` column to `auth_credentials`, with a partial unique index for the passkey kind, and a side table for the attributes. Not seven more nullable columns on a table already four wide with per-variant nulls. The split matches the model: a descriptor is identity and belongs with the credential, while a public key and a counter are attributes and do not.

That is the answer to open decision 18.3, and it should be written into the requirements in those terms. AUTH-4.4.2 promised that adding a credential kind would not be a schema rewrite. It holds for the credential type, where the descriptor is genuinely open, and not for storage, where the SQL table fans each variant out to its own columns. A passkey needs a migration whatever the domain model says.

Migrations ship paired up and down for both backends in the existing naming convention. `Store.Conformance` gains cases for each new operation, run against SQLite and Postgres, since it is the real gate on any backend.

## Phase 3: the protocol target

`AuthenticationPasskey`, a new `lean_lib` linking OpenSSL for the reason `AuthenticationOidc` does: a consumer taking only the magic link flow must link none of it.

It parses `authenticatorData`, which is fixed-layout binary, checks `clientDataJSON` through `lean-json`, reads the COSE key through `lean-cbor`, and verifies the signature.

The CBOR half is smaller than it looks, because `lean-cbor` already walks an attestation object down to its credential public key in its own suite. What is owed here is the fixed binary layout around it, the three `clientDataJSON` comparisons, the conversion of a COSE key into one the backend can verify with, and the verification itself.

Verification needs no new dependency, and less machinery than it first appears. `Leancrypto.Der.ecPublicKeyInfo` builds the `SubjectPublicKeyInfo` from a curve OID and a point, `Evp.PKey.fromSpki` loads it, and `Libcrypto.Sign.verify` takes the DER `SEQUENCE` an authenticator produces as it stands: going through JOSE and converting the signature to raw `R‖S` is unnecessary, because that conversion exists to meet JOSE's encoding and not OpenSSL's. ES256 first; RS256 and EdDSA are each a small addition after it.

## Phase 4: service operations

Begin and complete for each ceremony, plus a listing, a rename and a removal.

Registration requires a live session and is reached as the federated link route is reached, by a `POST` from the application's own pages, so that no request can name the account it attaches to. Removal goes through the same check as `unlinkIdentity`, which now has a second kind to count; the entry in `KNOWN_ISSUES.md` about that check being narrower than AUTH-6.8 asks is rewritten rather than deleted.

## Phase 5: routes

`AuthenticationPasskeyHttp`, four JSON endpoints under `/t/:tenant/passkey/`, in the `route_table` shape the federated routes use.

The two registration routes need a session and belong inside whatever wraps the browser half of the application. The two authentication routes carry no session and take the ceremony cookie instead.

## Phase 6: tests and vectors

A `test/fixtures/make-passkey-fixtures.sh`, beside the two scripts already there, capturing a registration and an authentication response once from a virtual authenticator over the DevTools protocol.

The decoding half of this is already covered upstream, where `lean-cbor` holds real attestation objects captured from YubiKey, Android, Apple and TPM authenticators. What the fixtures here have to cover is the ceremony rather than the bytes: the challenge bound to the attempt, the origin and the RP ID hash, and a signature that verifies.

Signatures are also generated by `openssl` over an independently constructed signing input. That is what gives the SNS fixtures their standing: the verifier is checked against bytes this repository cannot produce by the code path under test.

The limit goes in `KNOWN_ISSUES.md` in the same terms as the SNS entry. Vectors built against this library's reading of the specification would be consistently wrong across both halves, and only a real authenticator settles that.

Theorems not needed by production code live in test code.

## Phase 7: documentation

A requirements section with its own AUTH numbers, and 18.3 marked answered with what was decided. A target table row and a passkeys section in the README. Two rewrites in `KNOWN_ISSUES.md`. One sentence in the changelog.

## Breaking changes

Every consumer is affected, and a minor version is the least of it.

- `AuthStore` gains fields, so every backend implementing the port stops compiling.
- `CredentialKind` and `CredentialDescriptor` each gain a variant, so every exhaustive match downstream breaks.
- `PurgeCounts` gains a field.

## Risks

With Track A done the schedule risk has moved to Phase 2, where the conformance suite is the gate on every backend, and to Phase 6, where the vectors have to come from a real authenticator. Attestation is the scope risk, and the answer is to hold the line at the decision above. The user handle is still the irreversible one.

The quiet risk is Track B swallowing the whole effort, because the policy work is more interesting than the parsing work and is worth more.

## Sizing

Anchored on `AuthenticationOidc`, which is 1,215 lines of library and 659 of tests over three targets, the passkey targets land close to that, less whatever Phases 3 and 6 no longer owe. Store, migrations and conformance are mechanical but not small.

Order from here: Track B, then phases 1 to 7 in sequence.
