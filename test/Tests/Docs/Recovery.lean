/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Authentication
import Authentication.Instances

/-! The code of `docs/recovery.md`, checked by `Tests.Docs`. -/

namespace Tests.Docs.Recovery

open Authentication

def mailboxMoved {tenant : TenantId} (ports : Service.Ports IO) (account : AccountId tenant)
    (address : EmailAddress) : IO (Except StoreError Unit) :=
  Service.changePrimaryEmail ports account address

def issueRecovery {tenant : TenantId} (ports : Service.Ports IO) (config : TenantConfig tenant)
    (account : AccountId tenant) (administrator : String) :
    IO (Except Service.RecoveryRefusal (String × String)) := do
  match ← Service.createRecovery ports config account (createdBy := .client administrator) with
  | .error refusal => pure (.error refusal)
  | .ok issued => pure (.ok (issued.grant.id.value, issued.token.encoded))

def manage {tenant : TenantId} (ports : Service.Ports IO) (config : TenantConfig tenant)
    (account : AccountId tenant) (grant : RecoveryGrantId tenant) : IO Unit := do
  let _ ← Service.createRecovery ports config account (disposition := .keepExisting)
  let _ ← Service.recoveryGrants ports account
  let _ ← Service.revokeRecovery ports grant

end Tests.Docs.Recovery
