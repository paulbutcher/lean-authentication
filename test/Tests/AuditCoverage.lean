/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Authentication.Store.Conformance

namespace Tests.AuditCoverage

open Authentication Authentication.Store.Conformance

/-- What a backend has to tell apart about an event: its case, and which value of an enumeration
it carries. Identifiers are left out, because a backend stores every one of them as text. -/
def shape {tenant : TenantId} : AuditEvent tenant → Nat × Nat
  | .attemptCreated _ => (0, 0)
  | .linkOpened _ device => (1, device.ctorIdx)
  | .codeEntered _ outcome => (2, outcome.ctorIdx)
  | .attemptAbandoned _ reason => (3, reason.ctorIdx)
  | .sessionIssued _ => (4, 0)
  | .invitationConsumed _ => (5, 0)
  | .signInRejected outcome => (6, outcome.ctorIdx)
  | .sessionRevoked _ => (7, 0)
  | .accountSessionsRevoked _ reason => (8, reason.ctorIdx)
  | .primaryEmailChanged _ => (9, 0)
  | .accountDeactivated _ => (10, 0)
  | .accountReactivated _ => (11, 0)
  | .addressSuppressed _ reason => (12, reason.ctorIdx)
  | .suppressionCleared _ => (13, 0)
  | .consentGranted _ _ => (14, 0)
  | .consentWithdrawn _ _ => (15, 0)
  | .identityLinked _ _ => (16, 0)
  | .identityUnlinked _ _ => (17, 0)
  | .passkeyCounterRegressed _ _ => (18, 0)
  | .recoveryIssued _ _ => (19, 0)
  | .recoveryRedeemed _ _ => (20, 0)

/--
The conformance suite's audit round trip writes every kind of event there is, so a backend that
can store some kind in one direction only fails the suite rather than dropping that entry from
the log. A case added to `AuditEvent`, or a value added to an enumeration one carries, stops this
compiling until `everyAuditEvent` writes it too.

`shape e` names the case of `e` and the enumeration value it carries, and membership in the shapes
of `everyAuditEvent tenant` says the list holds an event of that case with that value. The claim is
for every event, so every case and every enumeration value. It rests on `shape` keeping cases
apart, which nothing proves; giving two cases one number would let one stand in for the other.
-/
theorem everyAuditEvent_complete (tenant : TenantId) (event : AuditEvent tenant) :
    shape event ∈ (everyAuditEvent tenant).map shape := by
  cases event <;> (try (rename_i payload; cases payload)) <;> simp [shape, everyAuditEvent]

end Tests.AuditCoverage
