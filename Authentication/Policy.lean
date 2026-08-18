/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Authentication.Email

namespace Authentication

/-- One policy per tenant (AUTH-7.1). -/
inductive SignupPolicy where
  | unrestricted
  | domainAllowlist (domains : List Domain) (includeSubdomains : Bool)
  | inviteOnly
  deriving DecidableEq, Repr, Inhabited

inductive SignupRejection where
  | domainNotAllowed
  | notInvited
  deriving DecidableEq, Repr, Inhabited

/-- Why an address that has proven itself was not signed in. Signup policy is one reason and a
deactivated account is the other; they are held apart because only the first is a decision about
whether an account may be made, and only the second concerns one that already exists
(AUTH-7.6, AUTH-9.6). -/
inductive SignInRefusal where
  | signup (reason : SignupRejection)
  | accountDeactivated
  deriving DecidableEq, Repr, Inhabited

inductive SignupDecision where
  | permitted
  | rejected (reason : SignupRejection)
  deriving DecidableEq, Repr, Inhabited

namespace SignupPolicy

/--
Evaluated at account creation only, so tightening a policy never locks out an account that
already exists (AUTH-7.6).

`invitationOverrides` is the per-tenant flag of AUTH-7.5: the two policies compose, so a tenant
can restrict self-signup to its own domains and still invite named outsiders.
-/
def evaluate (policy : SignupPolicy) (address : EmailAddress) (invitationAccepted : Bool)
    (invitationOverrides : Bool) : SignupDecision :=
  match policy with
  | .unrestricted => .permitted
  | .inviteOnly => if invitationAccepted then .permitted else .rejected .notInvited
  | .domainAllowlist domains includeSubdomains =>
    if domains.any (fun d => d.allows address.domain includeSubdomains) then .permitted
    else if invitationAccepted && invitationOverrides then .permitted
    else .rejected .domainNotAllowed

end SignupPolicy

end Authentication
