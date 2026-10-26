# Managing accounts and sessions

The shipped routes sign people in. Everything after that, knowing who is signed in, letting them sign out, and administering accounts, is a `Service` call your application makes. None of these calls checks permissions: the library has no roles, so deciding who may call each one is your application's job.

## Who is signed in

```lean
def signedIn {e : Routing.Engine} [Routing.ServerEngine e] {tenant : TenantId}
    (ports : Service.Ports IO) (config : TenantConfig tenant)
    (request : Std.Http.Request e.ReqBody) : IO (Option (AccountId tenant)) := do
  let some cookie := Http.cookieNamed request "auth_session" | pure none
  match ← Service.identify ports config ⟨cookie⟩ with
  | .ok identity => pure (some identity.account)
  | .error _ => pure none
```

`identify` answers the account and nothing else. Every way a credential can fail reaches you as one refusal, and `SessionRejection.name` tells them apart for a log. The cookie is only sent to paths under `TenantConfig.sessionCookiePath`, which is `/t/<tenant>` unless you widen it.

A session expires after `sessionIdleTimeout` unused, 14 days by default, and after `sessionAbsoluteLifetime` whatever happens, 90 days. Use is recorded at most every `sessionTouchInterval`, five minutes, so a session can expire up to that much earlier than its last use suggests.

## Signing out

No sign-out route ships. Revoke the session that asked, and clear the cookie in your response:

```lean
def signOut {tenant : TenantId} (ports : Service.Ports IO) (account : AccountId tenant)
    (credential : CredentialValue) : IO Unit := do
  for session in ← Service.sessions ports account (presented := some credential) do
    if session.current then
      discard <| Service.revokeSession ports account session.id
```

`Service.sessions` lists an account's live sessions with their user agent, coarse location and when each was last used, which is what a "where you're signed in" page shows. "Sign out everywhere else" is the same loop over the sessions that are not `current`. A revocation names the account as well as the session, so a session identifier taken from a request cannot sign out somebody else.

## Administering an account

```lean
let _ ← Service.changePrimaryEmail ports account address
let _ ← Service.deactivateAccount ports account
let _ ← Service.reactivateAccount ports account
Service.revokeAllSessions ports account
```

Changing the primary address and deactivating each sign the account out everywhere. A deactivated account cannot sign in again until reactivated. Tightening a tenant's signup or origin policy never ends sessions already live; `revokeAllSessions` is how you end them. An account that has lost its only way in is [recovered](recovery.md).

## Consent

The library stores consent but never asks for it: ask somebody already signed in, at a moment of your choosing, and record their answer.

```lean
let _ ← Service.grantConsent ports account ⟨"marketing"⟩ "2026-01"
let _ ← Service.withdrawConsent ports account ⟨"marketing"⟩ "2026-01"
let _ ← Service.consents ports account
let _ ← Service.consentHistory ports account
let _ ← Service.consenting (tenant := tenant) ports ⟨"marketing"⟩
```

The subject and the version are your own strings: the version records which wording the person saw. Record each consent separately, since one checkbox for both terms and marketing does not establish marketing consent. Withdrawing adds an entry rather than editing one, `consents` says where each subject stands now, and `consenting` lists the accounts a mailing may go to. Consent records are never removed.
