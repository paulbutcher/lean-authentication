/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Authentication

/-! The code of `docs/enforce-sso.md`, checked by `Tests.Docs`. -/

namespace Tests.Docs.Sso

open Authentication

private def config (tenant : TenantId) : TenantConfig tenant :=
  { displayName := "Acme"
    baseUrl := ⟨"https://app.example.com"⟩
    sendingIdentity := { address := ⟨"no-reply", ⟨["example", "com"]⟩⟩, displayName := "Acme" }
    signupPolicy := .unrestricted }

def ssoOnly (tenant : TenantId) : TenantConfig tenant :=
  { config tenant with originPolicy := .only [.federatedIdentity] }

def ssoOrPasskey (tenant : TenantId) : TenantConfig tenant :=
  { config tenant with originPolicy := .only [.federatedIdentity, .passkey] }

end Tests.Docs.Sso
