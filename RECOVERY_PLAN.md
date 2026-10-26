# Recovery plan

The work to answer open decision 18.1: what an administrator does about an account whose only way in is gone. The decisions are taken and nothing is built.

Most of 18.1 is already answered in code and not in the requirements. `Service.changePrimaryEmail` points an account at an address nobody has proven and revokes every session in the same call, so on a tenant that admits the magic link the administrator sets the new mailbox and the next link proves it. What has no answer is a tenant whose origin policy does not admit the magic link. There the administrator has no operation at all: `originPolicy` lives on `TenantConfig`, so the only lever is tenant-wide, and an invitation does not help because AUTH-8.8 routes it into a sign-in that AUTH-9.9.3 then refuses. A passkey-only tenant is where this bites, which is why passkeys opened it.

## Decisions

| Question | Answer |
| --- | --- |
| What a grant authorises | One credential enrolment, never a session |
| Delivery | Handed back to the caller, never mailed |
| Default lifetime | One hour, not the invitation's seven days |
| When sessions go | At issuance, as `RevocationReason.recovery` |
| When the grant is spent | On successful enrolment, not at ceremony start |
| Existing credentials | The caller chooses, default remove |
| Self-service | Still out of scope (§1.1) |

A grant authorises enrolment rather than a sign-in because that is what keeps it inside the model instead of carving an exception out of it. AUTH-9.9.5 already says adding a credential to an account is not constrained by the origin policy, since it issues no session; a grant inherits that reasoning exactly. The person enrols, then signs in with the new credential, and that sign-in is policy-checked like any other.

Nothing is mailed, because the premise of recovery is that the usual channel is gone. The token comes back to the client, which delivers it however it decided the person was who they said. This is the §13.2 line again, and the stakes are higher than an invitation's: an invitation token grants an account that does not exist yet, a recovery token grants one that does, with whatever is already in it. That asymmetry is what the one-hour default is for.

Sessions go when the grant is issued rather than when it is redeemed. AUTH-9.6 requires revocation on "any recovery action" and issuing the grant is the action; it costs nothing, because somebody who has lost their only credential holds no session worth keeping. This is what finally gives `RevocationReason.recovery` a producer.

The grant is spent on successful enrolment and not at the start of the ceremony, following `acceptInvitation`, which verifies without spending and leaves the invitation pending until a session is issued. The ceremony records carry a nullable grant column either way, because completion has to know whether to remove the account's other credentials and the disposition lives on the grant; spending at the start would narrow that column to a flag and buy nothing else. What late spending adds is that a fumbled ceremony leaves the grant pending, which is worth having because the person holding one has just lost a device and is meeting a dialog that fails for several ordinary reasons. What it costs is that a stolen token races the person to completion rather than being spent in front of them, so a failure looks like a fumble rather than like theft.

The grant id must not travel in the ceremony cookie instead. Completion would then be told which grant to spend by the party it is authorising, and somebody holding one valid grant could begin with it and name another at completion, enrolling onto an account they were never given.

## Phase 1: domain, store, schema, conformance

One phase rather than the two the passkey work needed. What forced that split was `CredentialDescriptor.passkey` breaking five SQL mappings before there was anywhere to put a passkey; nothing here adds a descriptor variant, so the record and its storage can land together.

A new `Authentication/Recovery.lean`, modelled on `Invitation` rather than on `FederationState`, because the shape wanted is a revocable, expiring, single-use grant with a state rather than a short-lived protocol record. `RecoveryGrant` holds the account, the token digest, the expiry, the state, the actor that created it, and the disposition. `RecoveryDisposition` is `removeExisting` or `keepExisting`. `RecoveryGrant.verify` mirrors `Invitation.verify`, and standing is derived rather than stored, as AUTH-8.9 has it for invitations.

`AuthStore` gains create, read by id, compare-and-set, a listing for one account, and a purge case; `PurgeCounts` gains a field. One `auth_recovery_grants` table paired up and down for both backends, appended to `createSchemaSql` in each and to the newest-first list in `test/Tests/Migrations.lean`. The Postgres up file is idempotent in every statement. Conformance cases for each operation, which is the real gate on both backends.

## Phase 2: service operations

`createRecovery` draws a token, writes the grant, revokes every session as `.recovery`, audits, and returns the token. `revokeRecovery` and a listing with standing complete the administrator's set. A `RecoveryRefusal` names the ways each can fail, as `InvitationRefusal` now does.

Two new `AuditEvent` cases, for issuing and for redeeming. They are the expensive part of this phase and the part worth care: `AuditEvent` is a closed inductive decoded by `auditColumns` and read back by `auditEventOf` in the shared SQL store, and the last time a case was added the two disagreed and a record read back as something else entirely. Both directions land together with a round-trip check.

Verification is shared rather than duplicated at each enrolment path: one internal operation turns a grant id and a presented token into an account or a refusal, and spends nothing.

## Phase 3: enrolment under a grant

`Passkey.beginRegistration` already takes an `AccountId`, and `beginFederated` already takes `account : Option (AccountId tenant)`. Both enrolment paths accept an account today; what is missing is only something that stands in for a session, so this phase is wiring rather than mechanism.

`PasskeyCeremony` and `FederationState` each gain an optional grant id, carried on the record and never supplied at completion, for the reason `FederationState.invitation` is carried there. Completion spends the grant under compare-and-set, applies the disposition, and audits. Removing the account's other credentials goes through the same path as `unlinkIdentity` and deliberately not through its last-way-in check: the grant is the administrator saying this is the way in now.

## Phase 4: routes

No new target. The passkey half belongs in `AuthenticationPasskeyHttp` because it links OpenSSL, the federated half in `AuthenticationOidcHttp` for the same reason, and both are already mounted by anyone who could need them.

They are separate routes from the enrolment routes rather than a flag on them, which is what keeps AUTH-22.21 true as written: the registration routes still read the account from the session and nowhere else. These read it from the grant and nowhere else. Every refusal answers one body, as AUTH-14.2.3 requires.

## Phase 5: documentation

18.1 marked answered with what was decided, and AUTH-9.10 and below carrying the requirements, since recovery is account lifecycle and §9 is where that lives. This earns no section of its own: §22 got one because passkeys were large and carried decisions that could not be revisited, and neither is true here.

A README section, the passkey-only entry removed from `KNOWN_ISSUES.md`, and one sentence in the changelog.

## Breaking changes

A minor version, and every consumer is affected.

- `AuthStore` gains fields, so every backend implementing the port stops compiling.
- `AuditEvent` gains two cases, so every exhaustive match downstream breaks, and both SQL backends need both directions.
- `PurgeCounts` gains a field.
- `PasskeyCeremony` and `FederationState` each gain a field, and their SQL mappings with it.

`changePrimaryEmail` keeps its signature and its meaning. Recovery on a tenant that admits the magic link is still that call, and this adds the case it never covered rather than replacing it.

## Risks

The grant is a bearer token standing in for an account that already exists, so a client that leaks one has handed somebody an account rather than merely an address. The library cannot make the client's delivery safe and should not pretend to: what it can do is keep the default lifetime short, make the grant single use and revocable, revoke the sessions up front, and record both ends in the audit log. That the delivery is the client's is worth stating in the README next to the operation rather than in a requirement nobody reads.

The scope risk is self-service. Every argument for a grant is an argument for letting the person ask for one themselves, and §1.1 rules that out for good reasons that have not changed.

## Sizing

Smaller than the passkey work and smaller than federation: no new target, no new dependency, no new protocol, and no new ceremony machinery. The closest anchor is the invitation feature, which is about 100 lines of `Service.lean`, 8 of the port, 45 of the SQL store, and one table. Add two audit cases in both directions, two optional columns on existing ceremony records, three routes, and the conformance cases.

Order: phases 1 to 5 in sequence. Nothing here is independent of what precedes it.
