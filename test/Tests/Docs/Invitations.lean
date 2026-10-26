/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Authentication
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

def invitedAs {tenant : TenantId} (ports : Service.Ports IO) (account : AccountId tenant) :
    IO (Option InvitationMetadata) := do
  let some held ← ports.store.accountById tenant account | pure none
  let invitations ← Service.invitations (tenant := tenant) ports
  pure <| invitations.findSome? fun (invitation, standing) =>
    if standing == .accepted && invitation.address.normalise == held.identity then
      some invitation.metadata
    else none

end Tests.Docs.Invitations
