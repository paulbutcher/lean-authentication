/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Authentication.Response

namespace Tests.Response
open Authentication

/--
AUTH-16.1 and AUTH-14.2.3: the default policy is constant. Whatever went wrong, and for whichever
tenant, the same thing is said and no notice is sent, so a client that configures nothing cannot
be used to enumerate addresses.

`uniformSilence` maps a tenant and a sign-in outcome to what the client should say. The two sides
share no arguments at all: the tenants differ and the outcomes differ, and the conclusion is
still an equality. That is what constant means here, and it is stronger than checking that the
known outcomes agree, because it also covers outcomes added later. It holds by `rfl`, so the
function ignores both arguments rather than mapping them all to the same value by cases.
-/
theorem uniformSilence_is_constant (tenant₁ tenant₂ : TenantId)
    (outcome₁ outcome₂ : SignInOutcome) :
    uniformSilence tenant₁ outcome₁ = uniformSilence tenant₂ outcome₂ := rfl

/--
The default the wiring produces is that policy, rather than one the documentation recommends
(AUTH-14.2.3). A safe default that a client has to opt into is not a default, and this is what
ties the `Inhabited` instance a client actually gets to the constant function above.

`(default : SignInResponsePolicy Id)` is the policy a client picks up by writing nothing, and
`.respond` is what the service calls with the tenant and the outcome. The conclusion equates it
with `uniformSilence` at the same arguments, for every tenant and every outcome, so the two
cannot drift apart. It holds by `rfl`, so the instance is that function rather than a copy of it
that a later edit could change on one side only.
-/
theorem default_policy_is_silent (tenant : TenantId) (outcome : SignInOutcome) :
    (default : SignInResponsePolicy Id).respond tenant outcome = uniformSilence tenant outcome :=
  rfl

end Tests.Response
