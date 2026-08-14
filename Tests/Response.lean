/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Authentication.Response

namespace Tests.Response
open Authentication

/-- AUTH-16.1 and AUTH-14.2.3: the default policy is constant. Whatever went wrong, and for
whichever tenant, the same thing is said and no notice is sent, so a client that configures
nothing cannot be used to enumerate addresses. -/
theorem uniformSilence_is_constant (tenant₁ tenant₂ : TenantId)
    (outcome₁ outcome₂ : SignInOutcome) :
    uniformSilence tenant₁ outcome₁ = uniformSilence tenant₂ outcome₂ := rfl

/-- The default the wiring produces is that policy, rather than one the documentation
recommends (AUTH-14.2.3). -/
theorem default_policy_is_silent (tenant : TenantId) (outcome : SignInOutcome) :
    (default : SignInResponsePolicy Id).respond tenant outcome = uniformSilence tenant outcome :=
  rfl

end Tests.Response
