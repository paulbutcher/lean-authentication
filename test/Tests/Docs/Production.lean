/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import AuthenticationHttp
import AuthenticationPostgres
import AuthenticationPostmark
import AuthenticationSes
import Authentication.Instances
import RoutingStd

/-! The code of `docs/production.md`, checked by `Tests.Docs`. -/

namespace Tests.Docs.Production

open Authentication

def pepper (keyId encoded : String) : Option Pepper :=
  (Leancrypto.Codec.Base64Url.decodeString encoded).map fun secret => { keyId := ⟨keyId⟩, secret }

def ports (db : Postgres.Connection) (peppers : PepperRing) (postmarkToken : String) :
    Service.Ports IO :=
  { store := Postgres.store db
    transport := Postmark.transport { serverToken := postmarkToken }
    responsePolicy := SignInResponsePolicy.silent IO
    limiter := Sql.rateLimiter Postgres.dialect (Postgres.connection db)
    responseFloor := ResponseFloor.sleeping 400
    humanCheck := HumanCheck.unchecked IO
    peppers }

def rotated (current previous : Pepper) : PepperRing :=
  { current, retired := [previous] }

def ses (credentials : Aws.Sigv4.Credentials) : EmailTransport IO :=
  Ses.transport { region := "eu-west-1", credentials }

def candid : SignInResponsePolicy IO :=
  { respond := fun _ outcome => pure <|
      match outcome with
      | .malformedAddress => { message := .addressMalformed, notice := none }
      | .throttled => { message := .tryAgainLater, notice := none }
      | _ => { message := .checkYourMail, notice := none } }

private def config (tenant : TenantId) : TenantConfig tenant :=
  { displayName := "Acme"
    baseUrl := ⟨"https://app.example.com"⟩
    sendingIdentity := { address := ⟨"no-reply", ⟨["example", "com"]⟩⟩, displayName := "Acme" }
    signupPolicy := .unrestricted }

def webhooks (hookPassword bouncesTopicArn : String) : List (WebhookEndpoint IO) :=
  [ Postmark.endpoint { username := "hook", password := hookPassword },
    Ses.endpoint (Ses.curlSubscription [bouncesTopicArn]) ]

def app (ports : Service.Ports IO) (hookPassword bouncesTopicArn : String) :
    Routing.StatelessHandler .std :=
  Middleware.forwardedRemoteAddr Middleware.Header.Name.xForwardedFor <| Http.handler
    { ports
      tenant := fun t => pure (some (config t))
      webhooks := webhooks hookPassword bouncesTopicArn }

def housekeeping (ports : Service.Ports IO) (tenants : List TenantId) : IO Unit := do
  for tenant in tenants do
    discard <| Service.purgeExpired (tenant := tenant) ports

end Tests.Docs.Production
