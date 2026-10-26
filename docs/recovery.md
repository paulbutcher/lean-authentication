# Recovering an account

Somebody has lost their only way in: the mailbox has gone, or the phone holding their passkey. There is no self-service recovery. Your application decides who the person is, by a support call or whatever else it trusts, and the library supplies the operation that lets them back in. It checks no permissions, so deciding who may recover an account is yours.

## Where the magic link is admitted

Point the account at the address the person can now read. The next magic link proves it:

```lean
def mailboxMoved {tenant : TenantId} (ports : Service.Ports IO) (account : AccountId tenant)
    (address : EmailAddress) : IO (Except StoreError Unit) :=
  Service.changePrimaryEmail ports account address
```

This signs the account out everywhere at the same moment.

## Where it is not

A tenant enforcing SSO, or admitting only passkeys, has no mail to send. There a recovery grant lets the account enrol exactly one new credential without a session:

```lean
def issueRecovery {tenant : TenantId} (ports : Service.Ports IO) (config : TenantConfig tenant)
    (account : AccountId tenant) (administrator : String) :
    IO (Except Service.RecoveryRefusal (String × String)) := do
  match ← Service.createRecovery ports config account (createdBy := .client administrator) with
  | .error refusal => pure (.error refusal)
  | .ok issued => pure (.ok (issued.grant.id.value, issued.token.encoded))
```

**The library does not deliver the grant, and never will.** It hands the grant's identifier and token back to you, and you pass them to the person by whatever channel established who they were. Treat them like a password reset link that bypasses the mailbox, because that is what they are. A grant expires after `TenantConfig.recoveryGrantLifetime`, an hour by default, and issuing one signs the account out everywhere.

The person redeems it at whichever enrolment the tenant offers. Both routes take the grant and token in the request body, never the query, so neither reaches an access log:

- **A passkey.** Post `{"grant": "...", "token": "..."}` to `/t/<tenant>/passkey/recover`, pass the options it answers to `navigator.credentials.create` as [registration](passkeys.md#the-script-is-yours) does, and post the result to `/t/<tenant>/passkey/recover/complete`.
- **A provider.** Post a form with fields `grant` and `token` to `/t/<tenant>/federated/<provider>/recover`; the provider's identity is linked to the account when it answers.

A grant authorises one enrolment and never a session, so the person then signs in with the new credential like anybody else. Recovering the provider account itself is the provider's job; a grant only links an identity afterwards.

## What happens to the old credentials

By default, enrolling under a grant removes every other way into the account, which is the moment a lost device stops working. Where you know the old credential is safe, keep it:

```lean
let _ ← Service.createRecovery ports config account (disposition := .keepExisting)
```

## Changing your mind

```lean
let _ ← Service.recoveryGrants ports account
let _ ← Service.revokeRecovery ports grant
```

`recoveryGrants` lists an account's grants as pending, spent, expired or revoked. A grant issued in error, or handed to the wrong person, can be revoked until it is redeemed.
