/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Authentication.Template

/-!
Bot mitigation on the send endpoint (AUTH-14.1.8).

A port and not an integration: Turnstile, hCaptcha and reCAPTCHA all work by putting a value in
the form and having the server ask the provider about it, and which provider that is has nothing
to do with authentication. What crosses this boundary is the value, as text, and an answer.

Chosen from configuration at startup, so a structure rather than a class (AUTH-3.5).
-/

namespace Authentication

structure HumanCheck (m : Type → Type) where
  /-- `none` when the request carried no proof at all, which a real implementation should treat
  as a failure rather than as an absent challenge: a client that has turned one on has a form
  that always carries the field. -/
  verify : RequestContext → Option String → m Bool

namespace HumanCheck

/-- Every request passes. This is the default the wiring produces, and it is the honest one: a
library that shipped a check would be shipping a provider. A deployment using it has not met
AUTH-14.1.8, and what stands between it and a flood is the rate limiter. -/
def unchecked (m : Type → Type) [Pure m] : HumanCheck m := ⟨fun _ _ => pure true⟩

instance {m : Type → Type} [Pure m] : Inhabited (HumanCheck m) := ⟨unchecked m⟩

end HumanCheck

end Authentication
