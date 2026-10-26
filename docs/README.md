# Use cases

Start with [Getting started](getting-started.md), which has email sign-in working on your own machine, and [Running in production](production.md), which replaces its development stand-ins. Everything else adds to those two.

## Who can join, and how they sign in

A tenant makes two independent choices. Its [signup policy](signup.md) says who may create an account; its [origin policy](enforce-sso.md) says what may sign somebody in. Each cell is a supported combination:

| Signs in with | Anyone | Your domains | Invited only |
| --- | --- | --- | --- |
| Magic link (the default) | Yes | Yes | Yes |
| Magic link or a [provider](federated-sign-in.md) | Yes | Yes, but an Apple relay address never matches | Yes |
| A provider only ([enforced SSO](enforce-sso.md)) | Yes | Yes | Yes, though the invitation names the first provider |
| Any of these, plus [passkeys](passkeys.md) | Yes | Yes | Yes |
| [Passkeys only](passkeys.md#passkeys-only) | Existing accounts only | Existing accounts only | Existing accounts only |

A passkey never creates an account, which is why the last row takes no new members. Whatever the policies, the first sign-in to succeed creates the account; there is no separate registration.

## Guides

| I want to | Guide |
| --- | --- |
| Let anyone, my organisation's domains, or only invited people sign up | [Choosing who can sign up](signup.md) |
| Invite people, and give them roles | [Inviting people](invitations.md) |
| Let people sign in with Google, Apple, GitHub or any OpenID Connect provider | [Federated sign-in](federated-sign-in.md) |
| Require my organisation's identity provider | [Enforcing single sign-on](enforce-sso.md) |
| Offer passkeys | [Passkeys](passkeys.md) |
| Know who is signed in, sign them out, change an address, deactivate, record consent | [Managing accounts and sessions](accounts.md) |
| Let somebody back in who has lost their mailbox or device | [Recovering an account](recovery.md) |
| Issue tokens to MCP clients and other OAuth clients | [Running an OAuth 2.1 authorisation server](authorisation-server.md) |

## Not supported

- Passwords in any form, and SMS.
- Self-service recovery: an administrator [recovers an account](recovery.md).
- SAML and SCIM, impersonation, and inbound mail.
- A hostname or sending domain per tenant: tenants share one origin and are told apart by path.
- ID tokens from the authorisation server, which is OAuth and not OpenID Connect.

[REQUIREMENTS.md](../REQUIREMENTS.md) is the specification these rest on, and [KNOWN_ISSUES.md](../KNOWN_ISSUES.md) records where the implementation deliberately falls short of it.
