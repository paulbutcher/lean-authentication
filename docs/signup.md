# Choosing who can sign up

Each tenant has one `SignupPolicy`, and it decides who may create an account. It is checked only when an account would be created: someone who already has an account signs in whatever the policy says now, so tightening a policy locks nobody out. Ending access for an existing account is [deactivating it](accounts.md).

The policy applies the same way to every route that can create an account, the magic link and [a federated provider](federated-sign-in.md) alike. A passkey never creates an account.

## Anyone

```lean
signupPolicy := .unrestricted
```

Any well-formed address may create an account. This is what [Getting started](getting-started.md) uses.

## Addresses at your organisation's domains

Domains usually come from configuration, as text:

```lean
def allowedDomains (configured : List String) : Except EmailError (List Domain) :=
  configured.mapM Domain.parse
```

```lean
def staffOnly (domains : List Domain) (tenant : TenantId) : TenantConfig tenant :=
  { config tenant with signupPolicy := .domainAllowlist domains (includeSubdomains := true) }
```

Matching is on whole labels, so `evilexample.com` never matches `example.com`. With `includeSubdomains`, `mail.example.com` matches as well. Domains are compared after case folding and punycode conversion, so a lookalike internationalised domain does not match. An Apple private relay address never satisfies an allowlist, because it is deliverable and says nothing about who holds it.

## Domains, and named outsiders

By default an invitation overrides the allowlist, so a tenant can restrict self-signup to its own staff and still invite a contractor at another domain:

```lean
def staffAndGuests (domains : List Domain) (tenant : TenantId) : TenantConfig tenant :=
  { staffOnly domains tenant with invitationOverridesAllowlist := true }
```

Turn the override off where even an invitation must not admit an outside address:

```lean
def strictlyStaff (domains : List Domain) (tenant : TenantId) : TenantConfig tenant :=
  { staffOnly domains tenant with invitationOverridesAllowlist := false }
```

## Invited people only

```lean
def invitedOnly (tenant : TenantId) : TenantConfig tenant :=
  { config tenant with signupPolicy := .inviteOnly }
```

An account is then created only by accepting an invitation, which [Inviting people](invitations.md) covers.

## What somebody refused is told

The policy is decided once the person has followed the link, never when they type an address: by then they have shown they hold the mailbox, so telling them why reveals nothing to anyone else. The sign-in page says the same thing whoever is asking, the mail goes out either way, and the page the link opens says they cannot sign in and why. `Http.Config.pages` replaces that page, and the audit log records the reason too.
