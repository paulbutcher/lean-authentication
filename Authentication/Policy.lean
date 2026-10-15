/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Authentication.Account
public import Authentication.Email

public section

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

/-- The operator's name for one, for a log record or a span attribute. -/
def SignupRejection.name : SignupRejection → String
  | .domainNotAllowed => "domain-not-allowed"
  | .notInvited => "not-invited"

/--
Which kinds of credential may originate a session, as distinct from which kinds an account may
hold. Turning the magic link off here is what stops it being a way around a tenant that has moved
to a provider; the addresses stay on the accounts and nothing stored changes.
-/
inductive OriginPolicy where
  | any
  /-- Nothing outside the list may originate a session, so an empty list admits nobody. -/
  | only (kinds : List CredentialKind)
  deriving DecidableEq, Repr, Inhabited

/-- Consulted where a session is issued and nowhere else, so tightening the policy refuses the
next sign-in rather than ending the sessions already live, as signup policy leaves alone the
accounts that already exist (AUTH-7.6). -/
def OriginPolicy.permits : OriginPolicy → CredentialKind → Bool
  | .any, _ => true
  | .only kinds, kind => kinds.contains kind

/-- Why an address that has proven itself was not signed in. The reasons are kept apart because
each decides a different question: whether an account may be made, whether one that already
exists may be used, whether the provider's word on the address is good, and whether this tenant
admits the means that proved it (AUTH-7.6, AUTH-9.6, AUTH-6.7). -/
inductive SignInRefusal where
  | signup (reason : SignupRejection)
  | accountDeactivated
  /-- The provider asserted an address it has not verified, so there is nothing to link on and
  nothing to create from (AUTH-6.7). -/
  | addressNotVerified
  /-- The address was proven, by a means this tenant does not admit. -/
  | originNotPermitted
  deriving DecidableEq, Repr, Inhabited

/-- The operator's name for one, for a log record or a span attribute. A signup reason keeps the
name it has there, so all three refusals are one set of names to group a query by. -/
def SignInRefusal.name : SignInRefusal → String
  | .signup reason => reason.name
  | .accountDeactivated => "account-deactivated"
  | .addressNotVerified => "address-not-verified"
  | .originNotPermitted => "origin-not-permitted"

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
    -- A relay address is refused here however the allowlist is written, which is what AUTH-6.9
    -- means by not satisfying one: the domain is the provider's, not the person's employer's.
    if !address.domain.isRelay
        && domains.any (fun d => d.allows address.domain includeSubdomains) then .permitted
    else if invitationAccepted && invitationOverrides then .permitted
    else .rejected .domainNotAllowed

end SignupPolicy

end Authentication
