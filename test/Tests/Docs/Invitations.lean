/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import AuthenticationHttp
import Authentication.Instances

/-! The code of `docs/invitations.md`, checked by `Tests.Docs`. -/

namespace Tests.Docs.Invitations

open Authentication

def inviteEditor {tenant : TenantId} (ports : Service.Ports IO) (config : TenantConfig tenant)
    (address : EmailAddress) (inviter : String) :
    IO (Except Service.InvitationRefusal (Service.InvitationIssued tenant)) :=
  Service.createInvitation ports config address ⟨"editor"⟩ (createdBy := .client inviter)

def manage {tenant : TenantId} (ports : Service.Ports IO) (config : TenantConfig tenant)
    (id : InvitationId tenant) : IO Unit := do
  let _ ← Service.invitations (tenant := tenant) ports
  let _ ← Service.resendInvitation ports config id
  let _ ← Service.revokeInvitation ports id

def assignRole {tenant : TenantId} (admitted : Service.AccountAdmitted tenant) : IO Unit :=
  match admitted.invitationMetadata with
  | some role => IO.println s!"{admitted.account.value} joins as {role.payload}"
  | none =>
    if admitted.firstInTenant then IO.println s!"{admitted.account.value} owns the tenant"
    else pure ()

def http (ports : Service.Ports IO) (tenant : (t : TenantId) → IO (Option (TenantConfig t))) :
    Http.Config :=
  { ports, tenant, onAdmitted := fun _ admitted => assignRole admitted }

end Tests.Docs.Invitations
