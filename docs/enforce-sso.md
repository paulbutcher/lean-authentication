# Enforcing single sign-on

An organisation that has moved to its own identity provider needs every sign-in to go through it, because that is where conditional access, device policy and offboarding live. A magic link that still works gets round all of them: a leaver's directory account is disabled, but their mailbox is not.

`TenantConfig.originPolicy` says which kinds of credential may start a session. That is separate from which kinds an account may hold. The default, `.any`, admits all of them.

```lean
def ssoOnly (tenant : TenantId) : TenantConfig tenant :=
  { config tenant with originPolicy := .only [.federatedIdentity] }
```

`.only` admits exactly the kinds it names, so `.only []` admits nobody. The policy is enforced where every session is issued, which no route bypasses, invitations included. It is also checked at each route's entry, so a route the tenant does not offer sends no mail and makes no round trip.

## Moving a tenant over

Order matters, because the magic link is how people reach their accounts until the switch.

1. Configure the provider, as in [Signing in with providers](federated-sign-in.md). People whose provider asserts the address on their account are matched to it at their first provider sign-in.
2. Ask everyone else, including anyone on Apple's Hide My Email, to add the provider to their account while signed in. Adding a credential issues no session, so the policy never refuses it.
3. Set `originPolicy`. Sessions already live are not ended; call `Service.revokeAllSessions` for each account if they should be.

After the switch, [invitations](invitations.md) link to the tenant's first provider, and an account that has lost its way in is [recovered by grant](recovery.md). `Service.unlinkIdentity` stops counting the primary address as a way in, so it refuses to remove somebody's last provider.

## Allowing passkeys too

```lean
def ssoOrPasskey (tenant : TenantId) : TenantConfig tenant :=
  { config tenant with originPolicy := .only [.federatedIdentity, .passkey] }
```

A passkey cannot create an account, so new people still arrive through the provider. A tenant admitting only passkeys can take no new members at all ([Passkeys](passkeys.md#passkeys-only)).
