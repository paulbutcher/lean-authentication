/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import AuthenticationHttp
import AuthenticationPasskeyHttp
import Authentication.Instances
import RoutingStd

/-! The code of `docs/passkeys.md`, checked by `Tests.Docs`. -/

namespace Tests.Docs.Passkeys

open Authentication

def config (tenant : TenantId) : TenantConfig tenant :=
  { displayName := "Acme"
    baseUrl := ⟨"https://app.example.com"⟩
    sendingIdentity := { address := ⟨"no-reply", ⟨["example", "com"]⟩⟩, displayName := "Acme" }
    passkeyRelyingParty := some
      { id := "example.com"                      -- or "app.example.com", and not changeable after
        origins := ["https://app.example.com"] }
    signupPolicy := .unrestricted }

def app (ports : Service.Ports IO) : Routing.StatelessHandler .std :=
  let tenant := fun t => pure (some (config t))
  Routing.toHandler
    (Http.routes { ports, tenant } ++
      PasskeyHttp.routes { ports, verifier := Passkey.verifier, tenant })

def manage {tenant : TenantId} (ports : Service.Ports IO) (config : TenantConfig tenant)
    (account : AccountId tenant) (id : CredentialId tenant) : IO Unit := do
  let _ ← Service.passkeys ports account
  let _ ← Service.renamePasskey ports account id "Work laptop"
  let _ ← Service.unlinkIdentity ports config account id

end Tests.Docs.Passkeys
