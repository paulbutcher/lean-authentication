/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import AuthenticationHttp
import AuthenticationSqlite
import Authentication.Instances
import RoutingStd

/-!
The code of `docs/getting-started.md`. `Tests.Docs` checks that every block the guide prints is
here, so a guide whose code has drifted from the library fails the build or the suite.
-/

namespace Tests.Docs.GettingStarted

open Authentication

def ports (db : SQLite) (pepper : ByteArray) : Service.Ports IO :=
  { store := Sqlite.store db
    transport := EmailTransport.console
    responsePolicy := SignInResponsePolicy.silent IO
    limiter := Sql.rateLimiter Sqlite.dialect (Sqlite.connection db)
    responseFloor := ResponseFloor.immediate IO
    humanCheck := HumanCheck.unchecked IO
    peppers := { current := { keyId := ⟨"development"⟩, secret := pepper } } }

def config (tenant : TenantId) : TenantConfig tenant :=
  { displayName := "Acme"
    baseUrl := ⟨"http://localhost:8080"⟩
    sendingIdentity := { address := ⟨"no-reply", ⟨["example", "com"]⟩⟩, displayName := "Acme" }
    signupPolicy := .unrestricted
    returnToAllowlist := ["/"] }

def main : IO Unit := do
  let db ← Sqlite.openInMemory
  let pepper ← IO.getRandomBytes 32
  let app : Routing.StatelessHandler .std :=
    Http.handler { ports := ports db pepper, tenant := fun t => pure (some (config t)) }
  let address : Std.Net.SocketAddress := .v4 { addr := .ofParts 127 0 0 1, port := 8080 }
  Std.Async.Async.block do
    let server ← Std.Http.Server.serve address app
    server.waitShutdown

end Tests.Docs.GettingStarted
