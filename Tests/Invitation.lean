/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Authentication.Invitation

namespace Tests.Invitation
open Authentication

variable {tenant : TenantId} {now : Timestamp} {invitation : Authentication.Invitation tenant}
  {presented : PresentedSecret}

/--
AUTH-16.1: consuming an invitation yields the invitation's own address, for every input. The
tenant travels with the type, so the second half of AUTH-8.3 is not a theorem here but a
typing rule: `InvitationGrant tenant` cannot name an account in another tenant.
-/
theorem grant_address_is_invitation_address
    {next : Authentication.Invitation tenant} {grant : InvitationGrant tenant}
    (h : Authentication.Invitation.consume now invitation presented = .ok (next, grant)) :
    grant.address = invitation.address := by
  simp only [Authentication.Invitation.consume] at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · split at h
      · simp at h
      · simp only [Except.ok.injEq, Prod.mk.injEq] at h
        simp [← h.2]

/-- Single use: what acceptance leaves behind is no longer pending (AUTH-8.5). -/
theorem consumed_is_not_pending
    {next : Authentication.Invitation tenant} {grant : InvitationGrant tenant}
    (h : Authentication.Invitation.consume now invitation presented = .ok (next, grant)) :
    next.state = .accepted := by
  simp only [Authentication.Invitation.consume] at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · split at h
      · simp at h
      · simp only [Except.ok.injEq, Prod.mk.injEq] at h
        simp [← h.1]

end Tests.Invitation
