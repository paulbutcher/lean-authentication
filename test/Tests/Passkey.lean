/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Authentication.Passkey

/-!
What the passkey domain can never do (§16, AUTH-16.1).

Everything here is a pure total function over decidable structure, so these are theorems rather
than checks, and compiling is passing.
-/

namespace Tests.Passkey
open Authentication

/--
An assertion naming a credential the store does not hold signs nobody in. There is no account to
sign in as, and the refusal is the one that says so rather than a mismatch, which is what lets an
operator tell a credential that was never registered from one presented against the wrong account.

`Passkey.decide assertion none` is the decision taken when the lookup for the asserted passkey id
found nothing. The equation holds for every assertion, so no field of one can turn an absent
credential into a sign-in.
-/
theorem unknown_credential_refuses {tenant : TenantId} (assertion : PasskeyAssertion) :
    Passkey.decide (tenant := tenant) assertion none = .refuse .unknownCredential := rfl

/--
A passkey signs in the account its own credential belongs to, and does so exactly when the
authenticator's user handle agrees with that account or is absent. This is the whole of what an
assertion may conclude: no input signs in a second account, and none signs in on a handle naming
somebody else, which is the takeover a user handle exists to prevent.

`Passkey.decide assertion (some credential)` is the decision taken when the store found the
credential the asserted passkey id names. The biconditional gives both directions, so the
disjunction is the whole of what reaches `signIn`: an authenticator offering no handle is trusted
on the credential alone, one offering the matching handle is trusted too, and nothing else is.
`credential.account` stands on both sides of the equation, which is what says the account signed
in is the credential's own rather than anything the assertion named.
-/
theorem signIn_iff_handle_agrees {tenant : TenantId} (assertion : PasskeyAssertion)
    (credential : Credential tenant) :
    Passkey.decide assertion (some credential) = .signIn credential.account ↔
      (assertion.userHandle = none ∨
        assertion.userHandle = some (Passkey.userHandle credential.account)) := by
  simp only [Passkey.decide]
  cases h : assertion.userHandle with
  | none => simp
  | some presented =>
    by_cases hp : presented = Passkey.userHandle credential.account
    · simp [hp]
    · simp [hp]

/--
A consumed ceremony is never usable again, whatever time it is asked about. This is the single-use
half of AUTH-15.4.3 stated over the record rather than over the store: a second request carrying
the same challenge finds a record that refuses on its own terms, before any compare and set is
reached.

`ceremony.consumed now` is the record a completed ceremony writes back, and `usable later` is the
test a read applies to it. The equation holds for every `later`, including one before the ceremony
expired and one before it was consumed, so no clock can make a spent ceremony live again.
-/
theorem consumed_is_never_usable {tenant : TenantId} (ceremony : PasskeyCeremony tenant)
    (now later : Timestamp) : (ceremony.consumed now).usable later = false := by
  simp [PasskeyCeremony.consumed, PasskeyCeremony.usable]

/--
An authenticator that keeps no counter never looks cloned. Both sides reporting zero is how
WebAuthn says a counter is unsupported, and it is the ordinary case for a passkey synced between
devices, so a rule that called it a regression would report a cloning signal on nearly every
sign-in.

`Passkey.regressed 0 0` is the test applied when neither the stored counter nor the presented one
is set. It answers `false`, so nothing is recorded against a credential that simply does not
count.
-/
theorem no_counter_never_regresses : Passkey.regressed 0 0 = false := by decide

/--
A counter is only ever reported as having regressed when it did not advance. This is the guarantee
that an honest authenticator is never flagged, and it is worth stating because the comparison is
`≤` rather than `<`: a counter that repeats is a regression, and one that moves must not be.

The hypothesis is that `Passkey.regressed` answered `true` for this pair, and the conclusion reads
the comparison back out of it: the presented counter is no greater than the stored one. Stated this
way round rather than as an implication from `stored < presented` because it is the direction an
operator reads a recorded regression by, and it needs no arithmetic to believe.
-/
theorem regressed_only_when_not_advanced (stored presented : UInt32)
    (h : Passkey.regressed stored presented = true) : presented ≤ stored := by
  simp [Passkey.regressed] at h
  exact h.2

end Tests.Passkey
