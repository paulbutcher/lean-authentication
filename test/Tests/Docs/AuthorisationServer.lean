/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import AuthenticationHttp
import AuthenticationOAuth
import AuthenticationSqlite
import Authentication.Instances
import RoutingStd

/-! The code of `docs/authorisation-server.md`, checked by `Tests.Docs`. -/

namespace Tests.Docs.AuthorisationServer

open Authentication

private def config (tenant : TenantId) : TenantConfig tenant :=
  { displayName := "Acme"
    baseUrl := ⟨"https://auth.example.com"⟩
    sendingIdentity := { address := ⟨"no-reply", ⟨["example", "com"]⟩⟩, displayName := "Acme" }
    signupPolicy := .unrestricted
    returnToAllowlist := ["/t/acme/oauth/authorize"] }

def oauthPorts (db : SQLite) (peppers : PepperRing) : OAuth.Service.Ports IO :=
  { store := Sqlite.store db
    oauth := OAuth.sqlOAuthStore Sqlite.dialect (Sqlite.connection db)
    peppers }

def oauthConfig (tenant : TenantId) : OAuth.OAuthConfig tenant :=
  OAuth.OAuthConfig.standard ⟨"https://auth.example.com"⟩ [⟨"files:read"⟩, ⟨"files:write"⟩]

def oauth (ports : OAuth.Service.Ports IO) : OAuth.Http.Config :=
  { ports
    tenant := fun t => pure (some (config t))
    oauth := fun t => pure (some (oauthConfig t))
    defaultScopes := some [⟨"files:read"⟩] }

def app (http : Http.Config) (oauth : OAuth.Http.Config) : Routing.StatelessHandler .std :=
  let split := OAuth.Http.routes oauth
  Routing.toHandler (Http.routes http ++ split.browser ++ split.client)

def authorised {tenant : TenantId} (ports : OAuth.Service.Ports IO) (bearer : String) :
    IO (Except String (OAuth.Service.TokenClaims tenant)) := do
  match ← OAuth.Service.verify ports ⟨bearer⟩ ⟨"https://mcp.example.com/mcp"⟩ [⟨"files:write"⟩] with
  | .ok claims => pure (.ok claims)
  | .error rejection => pure (.error (OAuth.Service.challenge rejection))

def privacy {tenant : TenantId} (ports : OAuth.Service.Ports IO) (account : AccountId tenant) :
    IO Unit := do
  for connection in ← OAuth.Service.connections ports account do
    discard <| OAuth.Service.revoke ports account connection.client connection.resource

def housekeeping (ports : OAuth.Service.Ports IO) (tenant : TenantId) : IO Unit := do
  discard <| OAuth.Service.pruneClients (tenant := tenant) ports (idle := Duration.days 30)

end Tests.Docs.AuthorisationServer
