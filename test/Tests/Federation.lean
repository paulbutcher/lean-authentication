/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Authentication.Federation

/-!
Theorems over the linking rule of AUTH-6.7, which is the adversarial case of AUTH-16.7 that the
pure layer can answer on its own.

A counterexample to any of these is an account takeover rather than a wrong-looking answer, which
is what puts them here as theorems rather than as examples (AUTH-16.1).
-/

namespace Tests.Federation
open Authentication

variable {tenant : TenantId} {assertion : ProviderAssertion}
  {linked : Option (Credential tenant)} {holder : Option (Account tenant)}

/--
An unverified assertion never links and never creates. This is AUTH-6.7's prohibition stated as
the only thing that could make it false: that some combination of stored rows turns an unverified
address into an account.

`assertion.addressVerified = false` is the provider declining to vouch for the address, and
`linked = none` says no credential is stored for this issuer and subject, which together are
exactly the case in which the address is the only evidence on offer. The conclusion is an equality
rather than a negation, so the decision is that refusal and not merely something other than a
link. `holder` is left unconstrained: whether or not an account already holds the address, and
whichever account it is, the answer is the same, which is the part a configuration must not be
able to move.
-/
theorem unverified_never_admits (hv : assertion.addressVerified = false) (hl : linked = none) :
    Federation.decide assertion linked holder = .refuse .addressNotVerified := by
  subst hl
  simp [Federation.decide, hv]

/--
Linking happens only on an address the provider verified. The theorem above forbids the unverified
case from one direction; this states the same boundary from the other, over every decision that
came back as a link.

The hypothesis is that `decide` answered `.link account` for some account, and the conclusion is
that the assertion carried `addressVerified = true`. Nothing constrains `linked` or `holder`, so
this holds for every combination of stored rows that could have produced a link, which is what
makes it a statement about the rule rather than about one path through it.
-/
theorem link_implies_verified {account : AccountId tenant}
    (h : Federation.decide assertion linked holder = .link account) :
    assertion.addressVerified = true := by
  unfold Federation.decide at h
  cases linked with
  | some _ => simp at h
  | none =>
    cases hv : assertion.addressVerified with
    | false => simp [hv] at h
    | true => rfl

/--
An identity already linked signs in as the account it is linked to, whatever the provider now says
about the address. This is AUTH-6.6 made checkable: the subject is the stable key, so an address
that has changed, or that the provider has stopped vouching for, moves nobody between accounts.

The hypothesis names a stored credential, and the conclusion is that the decision is `.signIn` of
that credential's own account. `assertion` is unconstrained, which is the whole content: no field
of it, `addressVerified` included, appears in the answer. `holder` is unconstrained too, so an
account holding the asserted address does not capture a session belonging to a different one.
-/
theorem linked_identity_is_the_account {credential : Credential tenant}
    (h : linked = some credential) :
    Federation.decide assertion linked holder = .signIn credential.account := by
  subst h
  rfl

/--
A verified assertion whose address nobody holds creates rather than refuses, so the rule turns
people away only for the reason AUTH-6.7 gives. Without this the three theorems above would be
satisfied by a function that refused everything.

`addressVerified = true` with `linked = none` and `holder = none` is the first sign-in of somebody
this tenant has never seen, and the conclusion is `.create`, which hands the decision to the
signup policy of AUTH-6.10 rather than settling it here.
-/
theorem verified_stranger_creates (hv : assertion.addressVerified = true) :
    Federation.decide assertion (tenant := tenant) none none = .create := by
  simp [Federation.decide, hv]

end Tests.Federation
