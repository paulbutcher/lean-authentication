/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import AuthenticationHttp
public import AuthenticationPasskey
public import Routing
import Middleware

/-!
The passkey routes (§18.3).

They answer JSON rather than pages, and that is the whole of the UI decision: `navigator.credentials`
cannot be driven from markup, so a page here would mean shipping a script, and the script belongs
to the application that knows what its sign-in looks like. What is served is the values a ceremony
needs and the verdict on what comes back.

Base64url throughout, because that is the form a page can put a `BufferSource` into JSON and the
form WebAuthn already uses for a credential id.
-/

public section

namespace Authentication.PasskeyHttp

open Std Http
open Std.Async
open Std.Http.Server
open Authentication.Http
open Authentication.Passkey

structure Config where
  ports : Service.Ports IO
  verifier : Verifier IO
  /-- The client's own lookup, as the other route sets take (AUTH-4.1.3). -/
  tenant : (t : TenantId) → IO (Option (TenantConfig t))
  /-- Where a refusal goes for the operator, since the response will not carry it
  (AUTH-14.2.6). The default does nothing, which is the only default that can be right. -/
  observeRefusal : TenantId → CeremonyRefusal → IO Unit := fun _ _ => pure ()

/-! ## Reading and writing JSON -/

private def headerValue (text : String) : Header.Value :=
  (Header.Value.ofString? text).getD default

private def guarded (response : Response Body.Any) : Response Body.Any :=
  let headers := response.line.headers
    |>.insert (Header.Name.mk "x-frame-options") (headerValue "DENY")
    |>.insert (Header.Name.mk "x-content-type-options") (headerValue "nosniff")
    |>.insert (Header.Name.mk "referrer-policy") (headerValue "no-referrer")
    |>.insert (Header.Name.mk "cache-control") (headerValue "no-store")
  { response with line := { response.line with headers } }

private def jsonResponse (status : Status) (payload : Json)
    (cookies : List Header.Value := []) : ContextAsync (Response Body.Any) := do
  let response ← Response.withStatus status |>.json payload.compress
  let headers := cookies.foldl (fun hs value => hs.insert setCookieName value)
    (guarded response).line.headers
  pure { response with line := { response.line with headers } }

/-- One body for every refusal, so that which of them it was is not readable from the response
(AUTH-14.2.3 takes the same position for the sign-in routes). The reason reaches the operator
through `observeRefusal` and nowhere else. -/
private def refusedBody : Json := Json.mkObj [("error", .str "rejected")]

private def refused (config : Config) (tenant : TenantId) (reason : CeremonyRefusal) :
    ContextAsync (Response Body.Any) := do
  _ ← (config.observeRefusal tenant reason : IO Unit)
  jsonResponse .badRequest refusedBody

private def notFound : ContextAsync (Response Body.Any) :=
  jsonResponse .notFound (Json.mkObj [("error", .str "not-found")])

private def stringMember (payload : Json) (name : String) : Option String :=
  (payload.getObjVal? name).toOption.bind (·.getStr?.toOption)

private def bytesMember (payload : Json) (name : String) : Option ByteArray :=
  (stringMember payload name).bind Leancrypto.Codec.Base64Url.decodeString

/-- `clientDataJSON` arrives base64url like the rest, and is UTF-8 text inside. Decoded here
rather than taken as a string, so a page sends every `BufferSource` the same way. -/
private def textMember (payload : Json) (name : String) : Option String :=
  (bytesMember payload name).bind fun bytes =>
    if h : bytes.IsValidUTF8 then some (String.fromUTF8 bytes h) else none

private def listMember (payload : Json) (name : String) : List String :=
  match (payload.getObjVal? name).toOption.bind (·.getArr?.toOption) with
  | none => []
  | some elements => elements.toList.filterMap (·.getStr?.toOption)

private def withTenant (config : Config)
    (body : (t : TenantId) → TenantConfig t → ContextAsync (Response Body.Any)) (raw : String) :
    ContextAsync (Response Body.Any) := do
  let tenant : TenantId := ⟨raw⟩
  match ← (config.tenant tenant : IO _) with
  | none => notFound
  | some tenantConfig => body tenant tenantConfig

/-- The account the request is signed in as, or none. Registration is reached only from a live
session, as a federated link is (AUTH-6.7.1). -/
private def signedInAs [Clock IO] (config : Config) {tenant : TenantId} (tenantConfig : TenantConfig tenant)
    (request : Request Body.Stream) : ContextAsync (Option (AccountId tenant)) := do
  match (cookieNamed request "auth_session").map (fun value => (⟨value⟩ : CredentialValue)) with
  | none => pure none
  | some credential =>
    match ← (Service.identify config.ports tenantConfig credential : IO _) with
    | .error _ => pure none
    | .ok identity => pure (some identity.account)

private def jsonPayload (request : Request Body.Stream) : ContextAsync (Option Json) := do
  match Json.parse (← request.body.readAll (α := String)) with
  | .error _ => pure none
  | .ok payload => pure (some payload)

/-! ## The options a ceremony answers with -/

private def credentialDescriptor (handle : PasskeyId) : Json :=
  Json.mkObj [("type", .str "public-key"), ("id", .str handle.value)]

/-- `residentKey` is required because this library registers discoverable credentials only: an
authenticator that will not make one is better refused at registration than found wanting at a
sign-in that has no address to fall back on. -/
private def registrationJson {tenant : TenantId} (tenantConfig : TenantConfig tenant)
    (options : RegistrationOptions) : Json :=
  Json.mkObj
    [ ("challenge", .str options.challenge.encoded),
      ("rp", Json.mkObj
        [("id", .str options.relyingParty.id), ("name", .str tenantConfig.displayName)]),
      ("user", Json.mkObj
        [ ("id", .str options.userHandle),
          ("name", .str options.userName),
          ("displayName", .str options.userName) ]),
      ("pubKeyCredParams", .arr
        #[Json.mkObj [("type", .str "public-key"), ("alg", .num (-7))]]),
      ("authenticatorSelection", Json.mkObj
        [("residentKey", .str "required"), ("userVerification", .str "preferred")]),
      ("excludeCredentials", .arr (options.exclude.map credentialDescriptor).toArray) ]

private def assertionJson (options : AssertionOptions) : Json :=
  Json.mkObj
    [ ("challenge", .str options.challenge.encoded),
      ("rpId", .str options.relyingParty.id),
      ("userVerification", .str "preferred") ]

/-! ## The routes -/

/--
Begins a registration for the account the request is signed in as.

A `POST` carrying no body, and its forgery defence is the session cookie's: `SameSite=Lax` is not
sent on a cross-site `POST`, so a request provoked from another site arrives signed in as nobody
and starts nothing (AUTH-6.7.1 gives the same reasoning for a federated link).
-/
def beginRegistration [Clock IO] [RandomBytes IO] (config : Config) (raw : String) :
    Routing.Result := fun request =>
  withTenant config (fun tenant tenantConfig => do
    match ← signedInAs config tenantConfig request with
    | none => refused config tenant .notThisAccount
    | some account =>
      match ← (Service.beginRegistration config.ports tenantConfig account : IO _) with
      | .error reason => refused config tenant reason
      | .ok options =>
        let now ← (Clock.now : IO _)
        jsonResponse .ok (registrationJson tenantConfig options) [setCookie now options.cookie])
    raw

def completeRegistration [Clock IO] [RandomBytes IO] (config : Config) (raw : String) :
    Routing.Result := fun request =>
  withTenant config (fun tenant tenantConfig => do
    match ← signedInAs config tenantConfig request with
    | none => refused config tenant .notThisAccount
    | some account =>
      match ← jsonPayload request with
      | none => refused config tenant .unknownCeremony
      | some payload =>
        match cookieNamed request "auth_passkey",
            bytesMember payload "attestationObject", textMember payload "clientDataJSON" with
        | some cookie, some attestation, some clientData =>
          match ← (Service.completeRegistration config.ports tenantConfig account cookie
              attestation clientData ((stringMember payload "label").getD "")
              (listMember payload "transports") : IO _) with
          | .error reason => refused config tenant reason
          | .ok registration =>
            jsonResponse .ok (Json.mkObj
              [("label", .str registration.label),
               ("backedUp", .bool registration.backupState)])
        | _, _, _ => refused config tenant .unknownCeremony)
    raw

/-- Begins an authentication. No session is needed and none is read: which account this signs in
is settled by the assertion, not by whoever asks for a challenge. -/
def beginAuthentication [Clock IO] [RandomBytes IO] (config : Config) (raw : String) :
    Routing.Result := fun request =>
  withTenant config (fun tenant tenantConfig => do
    match ← (Service.beginAuthentication config.ports tenantConfig
        (request.line.uri.query.get "returnTo") : IO _) with
    | .error reason => refused config tenant reason
    | .ok options =>
      let now ← (Clock.now : IO _)
      jsonResponse .ok (assertionJson options) [setCookie now options.cookie])
    raw

/-- Completes an authentication and issues the session cookie. `returnTo` comes off the ceremony
record rather than the request, and is still the client's to validate against the tenant's
allowlist before it redirects (AUTH-9.8). -/
def completeAuthentication [Clock IO] [RandomBytes IO] (config : Config) (raw : String) :
    Routing.Result := fun request =>
  withTenant config (fun tenant tenantConfig => do
    match ← jsonPayload request with
    | none => refused config tenant .unknownCeremony
    | some payload =>
      match cookieNamed request "auth_passkey", stringMember payload "id",
          bytesMember payload "authenticatorData", textMember payload "clientDataJSON",
          bytesMember payload "signature" with
      | some cookie, some handle, some authData, some clientData, some signature =>
        match ← (Service.completeAuthentication config.ports config.verifier tenantConfig cookie
            ⟨handle⟩ (stringMember payload "userHandle") authData clientData signature
            (requesterOf request) : IO _) with
        | .error reason => refused config tenant reason
        | .ok outcome =>
          let now ← (Clock.now : IO _)
          jsonResponse .ok
            (Json.mkObj [("signedIn", .bool outcome.session.isSome)])
            (outcome.setCookies.map (setCookie now))
      | _, _, _, _, _ => refused config tenant .unknownCeremony)
    raw

route_table Passkey [
  register := "/t/:tenant:String/passkey/register",
  registerComplete := "/t/:tenant:String/passkey/register/complete",
  signIn := "/t/:tenant:String/passkey/signin",
  signInComplete := "/t/:tenant:String/passkey/signin/complete"
]

@[expose] def routes [Clock IO] [RandomBytes IO] (config : Config) :
    List (Routing.Route Routing.Result) :=
  [ .post Passkey.patterns.register (beginRegistration config),
    .post Passkey.patterns.registerComplete (completeRegistration config),
    .post Passkey.patterns.signIn (beginAuthentication config),
    .post Passkey.patterns.signInComplete (completeAuthentication config) ]

/-- Mount this wherever the application's own router is, as the other route sets are mounted. The
two registration routes need a session; the two authentication routes do not, and must not be put
behind a guard that requires one. -/
def handler [Clock IO] [RandomBytes IO] (config : Config) : StatelessHandler :=
  Routing.toHandler (routes config) (fun _ => notFound)

end Authentication.PasskeyHttp
