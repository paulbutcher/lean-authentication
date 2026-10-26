/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Authentication

/-! The code of `docs/signup.md`, checked by `Tests.Docs`. -/

namespace Tests.Docs.Signup

open Authentication

private def config (tenant : TenantId) : TenantConfig tenant :=
  { displayName := "Acme"
    baseUrl := ⟨"https://app.example.com"⟩
    sendingIdentity := { address := ⟨"no-reply", ⟨["example", "com"]⟩⟩, displayName := "Acme" }
    signupPolicy := .unrestricted
    returnToAllowlist := ["/"] }

def allowedDomains (configured : List String) : Except EmailError (List Domain) :=
  configured.mapM Domain.parse

def staffOnly (domains : List Domain) (tenant : TenantId) : TenantConfig tenant :=
  { config tenant with signupPolicy := .domainAllowlist domains (includeSubdomains := true) }

def staffAndGuests (domains : List Domain) (tenant : TenantId) : TenantConfig tenant :=
  { staffOnly domains tenant with invitationOverridesAllowlist := true }

def strictlyStaff (domains : List Domain) (tenant : TenantId) : TenantConfig tenant :=
  { staffOnly domains tenant with invitationOverridesAllowlist := false }

def invitedOnly (tenant : TenantId) : TenantConfig tenant :=
  { config tenant with signupPolicy := .inviteOnly }

end Tests.Docs.Signup
