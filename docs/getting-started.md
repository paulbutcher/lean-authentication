# Getting started

Email sign-in on your own machine: magic links, an in-memory SQLite database, and mail printed to the console instead of sent. [Running in production](production.md) replaces each of those stand-ins.

## Install

```toml
[[require]]
name = "authentication"
git = "https://github.com/paulbutcher/lean-authentication"

[[require]]
name = "routing-std"
git = "https://github.com/paulbutcher/lean-routing"
subDir = "std"
```

Each target is a separate `lean_lib`, and you depend only on what you use. This guide needs three of them:

```lean
import AuthenticationHttp
import AuthenticationSqlite
import Authentication.Instances
import RoutingStd
```

`Authentication.Instances` supplies `Clock` and `RandomBytes` from the host's wall clock and the operating system's random source. They are low priority, so an instance of your own wins wherever it is in scope.

## Wire the ports

Everything the library reaches outside itself goes through a port you construct. In development:

```lean
def ports (db : SQLite) (pepper : ByteArray) : Service.Ports IO :=
  { store := Sqlite.store db
    transport := EmailTransport.console
    responsePolicy := SignInResponsePolicy.silent IO
    limiter := Sql.rateLimiter Sqlite.dialect (Sqlite.connection db)
    responseFloor := ResponseFloor.immediate IO
    humanCheck := HumanCheck.unchecked IO
    peppers := { current := { keyId := ⟨"development"⟩, secret := pepper } } }
```

`EmailTransport.console` prints each message, sign-in link included, so anyone who can read the console can sign in as anybody who asked. The pepper is the server-side key every stored credential is digested under.

## Configure a tenant

A tenant is one organisation using your application, and everything that varies between organisations is its `TenantConfig`. An address in two tenants is two unrelated accounts. Tenants are told apart by a path prefix, so Acme signs in at `/t/acme/signin`.

```lean
def config (tenant : TenantId) : TenantConfig tenant :=
  { displayName := "Acme"
    baseUrl := ⟨"http://localhost:8080"⟩
    sendingIdentity := { address := ⟨"no-reply", ⟨["example", "com"]⟩⟩, displayName := "Acme" }
    signupPolicy := .unrestricted
    returnToAllowlist := ["/"] }
```

Here every tenant gets the same configuration and anyone may sign up. In a real application `tenant` looks the organisation up and answers `none` for one you do not recognise, which is a `404`.

## Serve the routes

```lean
def main : IO Unit := do
  let db ← Sqlite.openInMemory
  let pepper ← IO.getRandomBytes 32
  let app : Routing.StatelessHandler .std :=
    Http.handler { ports := ports db pepper, tenant := fun t => pure (some (config t)) }
  let address : Std.Net.SocketAddress := .v4 { addr := .ofParts 127 0 0 1, port := 8080 }
  Std.Async.Async.block do
    let server ← Std.Http.Server.serve address app
    server.waitShutdown
```

Open `http://localhost:8080/t/acme/signin`, enter an address, and follow the link the console prints. Opened in the same browser, it asks you to confirm; opened anywhere else, it shows a code to type into the browser you started in, and signs nobody in where it was opened.

The first sign-in to succeed creates the account; there is no registration step. The session cookie is scoped to `/t/acme` by default, and `TenantConfig.sessionCookiePath` widens it to cover your application. `Http.routes` returns the same routes as a list, for mounting beside your own, and `Http.Config.pages` replaces the default pages, which are unstyled and semantic.

## Find out who is signed in

The shipped routes issue the session; every request after that is yours to authenticate. `Service.identify` takes the credential from the session cookie and answers the account and its tenant, and nothing else: what that account may do is your application's to decide. [Managing accounts](accounts.md) has the rest of the session operations.

## Next

[Choose a use case](README.md), or go straight to [running in production](production.md).
