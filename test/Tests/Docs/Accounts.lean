/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import AuthenticationHttp
import Authentication.Instances

/-! The code of `docs/accounts.md`, checked by `Tests.Docs`. -/

namespace Tests.Docs.Accounts

open Authentication

def signedIn {e : Routing.Engine} [Routing.ServerEngine e] {tenant : TenantId}
    (ports : Service.Ports IO) (config : TenantConfig tenant)
    (request : Std.Http.Request e.ReqBody) : IO (Option (AccountId tenant)) := do
  let some cookie := Http.cookieNamed request "auth_session" | pure none
  match ← Service.identify ports config ⟨cookie⟩ with
  | .ok identity => pure (some identity.account)
  | .error _ => pure none

def signOut {tenant : TenantId} (ports : Service.Ports IO) (account : AccountId tenant)
    (credential : CredentialValue) : IO Unit := do
  for session in ← Service.sessions ports account (presented := some credential) do
    if session.current then
      discard <| Service.revokeSession ports account session.id

def signOutElsewhere {tenant : TenantId} (ports : Service.Ports IO) (account : AccountId tenant)
    (credential : CredentialValue) : IO Unit := do
  for session in ← Service.sessions ports account (presented := some credential) do
    if !session.current then
      discard <| Service.revokeSession ports account session.id

def administer {tenant : TenantId} (ports : Service.Ports IO) (account : AccountId tenant)
    (address : EmailAddress) : IO Unit := do
  let _ ← Service.changePrimaryEmail ports account address
  let _ ← Service.deactivateAccount ports account
  let _ ← Service.reactivateAccount ports account
  Service.revokeAllSessions ports account

def marketing {tenant : TenantId} (ports : Service.Ports IO) (account : AccountId tenant) :
    IO Unit := do
  let _ ← Service.grantConsent ports account ⟨"marketing"⟩ "2026-01"
  let _ ← Service.withdrawConsent ports account ⟨"marketing"⟩ "2026-01"
  let _ ← Service.consents ports account
  let _ ← Service.consentHistory ports account
  let _ ← Service.consenting (tenant := tenant) ports ⟨"marketing"⟩

end Tests.Docs.Accounts
