/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Authentication.Tenant

/-!
What a person is told when a sign-in cannot proceed (AUTH-14.2).

The policy is asked only before any mail is sent, so the outcomes it sees are the ones decidable
without knowing who holds the address: a malformed address, a limit, suppression, and a route the
tenant does not offer. Whether the address has an account, or may create one, is decided once it
is proven, and recorded under the same type in the audit log (AUTH-14.2.6). Of the outcomes the
policy sees, only `addressSuppressed` says anything about a person (AUTH-14.2.8).
-/

public section

namespace Authentication

inductive SignInOutcome where
  | linkSent
  | notInvited
  | domainNotAllowed
  | addressSuppressed
  | accountDeactivated
  /-- A provider asserted an address it had not verified (AUTH-6.7). Reached only by the
  federated route, and present here so that route reports through the same type as the other
  (AUTH-14.2.7). -/
  | addressNotVerified
  /-- The address was proven by a means the tenant's origin policy does not admit. It describes
  the tenant rather than the person, so it is among the outcomes usually safe to state openly. -/
  | originNotPermitted
  | throttled
  | malformedAddress
  deriving DecidableEq, Repr, Inhabited

inductive SignInMessage where
  | checkYourMail
  | tryAgainLater
  | addressMalformed
  /-- For a client that would rather say an account is closed than let someone keep asking a
  mailbox that will never answer. Saying it confirms the account exists, which is why it is a
  choice and not the default. -/
  | accountUnavailable
  deriving DecidableEq, Repr, Inhabited

structure SignInResponse where
  message : SignInMessage
  deriving DecidableEq, Repr, Inhabited

/-- Selected at startup from configuration, so a structure rather than a class (AUTH-3.5).
`respond` is given the tenant so a client can vary behaviour per tenant without the library
holding a knob for it. -/
structure SignInResponsePolicy (m : Type → Type) where
  respond : TenantId → SignInOutcome → m SignInResponse

/-- Every outcome produces the same response. This is the default the wiring
uses, so a client that configures nothing is enumeration-resistant (AUTH-14.2.3). -/
def uniformSilence (_tenant : TenantId) (_outcome : SignInOutcome) : SignInResponse :=
  { message := .checkYourMail }

namespace SignInResponsePolicy

instance {m : Type → Type} [Pure m] : Inhabited (SignInResponsePolicy m) :=
  ⟨{ respond := fun tenant outcome => pure (uniformSilence tenant outcome) }⟩

def silent (m : Type → Type) [Pure m] : SignInResponsePolicy m :=
  { respond := fun tenant outcome => pure (uniformSilence tenant outcome) }

end SignInResponsePolicy

end Authentication
