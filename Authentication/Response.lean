/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Authentication.Tenant

/-!
What a person is told when a sign-in cannot proceed (AUTH-14.2).

The trade-off, so that a client can take it deliberately (AUTH-14.2.8): `domainNotAllowed` and
the fact that a tenant is invitation-only describe the tenant and say nothing about any
individual, so they are usually safe to state openly. `unknownAddress` and `notInvited`
identify people, and are the part worth protecting. Rate limiting does more work here than
wording does: at a few probes an hour any oracle is nearly worthless.
-/

namespace Authentication

inductive SignInOutcome where
  | linkSent
  | unknownAddress
  | notInvited
  | domainNotAllowed
  | addressSuppressed
  | accountDeactivated
  | throttled
  | malformedAddress
  deriving DecidableEq, Repr, Inhabited

inductive SignInMessage where
  | checkYourMail
  | addressNotRecognised
  | invitationRequired
  | domainNotAllowed
  | tryAgainLater
  | addressMalformed
  /-- For a client that would rather say an account is closed than let someone keep asking a
  mailbox that will never answer. Saying it confirms the account exists, which is why it is a
  choice and not the default. -/
  | accountUnavailable
  deriving DecidableEq, Repr, Inhabited

/-- Mail sent in place of a sign-in link, for a client that would rather explain by mail than
on the page. -/
inductive NoticeKind where
  | noAccountExists
  | signupNotPermitted
  deriving DecidableEq, Repr, Inhabited

structure SignInResponse where
  message : SignInMessage
  notice : Option NoticeKind
  deriving DecidableEq, Repr, Inhabited

/-- Selected at startup from configuration, so a structure rather than a class (AUTH-3.5).
`respond` is given the tenant so a client can vary behaviour per tenant without the library
holding a knob for it. -/
structure SignInResponsePolicy (m : Type → Type) where
  respond : TenantId → SignInOutcome → m SignInResponse

/-- Every outcome produces the same response and no notice. This is the default the wiring
uses, so a client that configures nothing is enumeration-resistant (AUTH-14.2.3). -/
def uniformSilence (_tenant : TenantId) (_outcome : SignInOutcome) : SignInResponse :=
  { message := .checkYourMail, notice := none }

namespace SignInResponsePolicy

instance {m : Type → Type} [Pure m] : Inhabited (SignInResponsePolicy m) :=
  ⟨{ respond := fun tenant outcome => pure (uniformSilence tenant outcome) }⟩

def silent (m : Type → Type) [Pure m] : SignInResponsePolicy m :=
  { respond := fun tenant outcome => pure (uniformSilence tenant outcome) }

end SignInResponsePolicy

end Authentication
