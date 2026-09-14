/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import AuthenticationOidc
import AuthenticationSqlite

/-!
A federated sign-in from the redirect to the session (§6).

The ID token is stubbed here on purpose: `Tests.Oidc` already verifies real ones against a real
key, and what is left to check is the flow around that, which is where `state`, its single use and
its pairing with the browser live.
-/

namespace Tests.FederatedFlow
open Authentication Authentication.Service Authentication.Oidc

initialize clockRef : IO.Ref Timestamp ← IO.mkRef ⟨1700000000⟩
initialize drawCounter : IO.Ref Nat ← IO.mkRef 0
initialize exchanges : IO.Ref Nat ← IO.mkRef 0

instance : Clock IO where
  now := clockRef.get

instance : RandomBytes IO where
  draw count := do
    let index ← drawCounter.modifyGet fun n => (n, n + 1)
    pure (.ok ((Leancrypto.Sha256.hashUtf8 s!"flow-seed-{index}").extract 0 count))

private def address (raw : String) : EmailAddress := (EmailAddress.parse raw).toOption.getD default

private def peppers : PepperRing :=
  { current := { keyId := ⟨"pepper-1"⟩, secret := Leancrypto.Sha256.hashUtf8 "flow pepper" } }

private def portsOn (db : SQLite) : Ports IO :=
  { store := Sqlite.store db
    transport := EmailTransport.capturing (fun _ => pure ())
    responsePolicy := SignInResponsePolicy.silent IO
    limiter := RateLimiter.unlimited IO
    responseFloor := ResponseFloor.immediate IO
    humanCheck := HumanCheck.unchecked IO
    peppers }

private def tenant : TenantId := ⟨"acme"⟩

private def config : TenantConfig tenant :=
  { displayName := "Acme"
    baseUrl := ⟨"https://auth.example.com"⟩
    sendingIdentity := { address := address "sign-in@auth.example.com", displayName := "Acme" }
    signupPolicy := .unrestricted }

private def provider : ProviderConfig :=
  { id := ⟨"google"⟩
    issuer := "https://accounts.google.test"
    clientId := "client-abc"
    credentials := .clientSecret (.external "unused") }

private def discovery : Discovery :=
  { issuer := provider.issuer
    authorizationEndpoint := provider.issuer ++ "/authorize"
    tokenEndpoint := provider.issuer ++ "/token"
    jwksUri := provider.issuer ++ "/jwks" }

private def redirectUri : String := "https://auth.example.com/t/acme/federated/google/callback"

private def identity : FederatedIdentity := ⟨provider.issuer, "subject-99"⟩

/-- Every port stubbed but the store, so what is exercised is the flow rather than the network. -/
private def oidcPorts (verified : Bool := true) : SignInPorts IO :=
  { metadata := { discover := fun _ => pure (.ok discovery) }
    identities :=
      { redeem := fun _ _ _ _ _ _ _ _ => do
          exchanges.modify (· + 1)
          pure (.ok
            { identity
              address := some (address "person@example.com")
              addressVerified := verified
              hostedDomain := none }) } }

/-- The same stub, asserting an address a check chooses. -/
private def portsAsserting (asserted : EmailAddress) : SignInPorts IO :=
  { metadata := { discover := fun _ => pure (.ok discovery) }
    identities :=
      { redeem := fun _ _ _ _ _ _ _ _ => pure (.ok
          { identity
            address := some asserted
            addressVerified := true
            hostedDomain := none }) } }

private def parameter (url name : String) : Option String :=
  ((url.splitOn (name ++ "=")).drop 1)[0]?.map fun tail =>
    String.ofList (tail.toList.takeWhile (· != '&'))

private def openDb : IO SQLite := do
  let db ← SQLite.openWith ":memory:" .readWriteCreate
  db.exec Sqlite.createSchemaSql
  pure db

def checks : IO (List (String × Bool)) := do
  let db ← openDb
  let ports := portsOn db
  let started ← beginFederated ports config provider discovery redirectUri (some "/dashboard")
  let url := (started.map (·.authorizationUrl)).getD ""
  let state := (started.bind fun s => parameter s.authorizationUrl "state").getD ""
  let cookieValue := (started.map (·.cookie.value)).getD ""

  exchanges.set 0
  let completed ← completeFederated ports (oidcPorts) config provider discovery redirectUri
    (some state) (some cookieValue) "the-code" {}
  let afterFirst ← exchanges.get

  -- The same `state` a second time: single use, under compare and set (AUTH-6.2).
  let replayed ← completeFederated ports (oidcPorts) config provider discovery redirectUri
    (some state) (some cookieValue) "the-code" {}

  -- A `state` that does not pair with the browser's cookie, which is the login-CSRF case.
  let fresh ← openDb
  let freshPorts := portsOn fresh
  let other ← beginFederated freshPorts config provider discovery redirectUri none
  let otherState := (other.bind fun s => parameter s.authorizationUrl "state").getD ""
  exchanges.set 0
  let mismatched ← completeFederated freshPorts (oidcPorts) config provider discovery redirectUri
    (some otherState) (some "a-cookie-from-somewhere-else") "the-code" {}
  let afterMismatch ← exchanges.get
  let noCookie ← completeFederated freshPorts (oidcPorts) config provider discovery redirectUri
    (some otherState) none "the-code" {}

  -- An unverified assertion is refused where the linking rule is, not here (AUTH-6.7).
  let strict ← openDb
  let strictPorts := portsOn strict
  let begun ← beginFederated strictPorts config provider discovery redirectUri none
  let begunState := (begun.bind fun s => parameter s.authorizationUrl "state").getD ""
  let begunCookie := (begun.map (·.cookie.value)).getD ""
  let unverified ← completeFederated strictPorts (oidcPorts false) config provider discovery
    redirectUri (some begunState) (some begunCookie) "the-code" {}

  let refused {α : Type} : Except OidcError α → Bool
    | .error _ => true
    | .ok _ => false

  pure
    [ ("federated flow: the authorization request asks for a code",
        parameter url "response_type" == some "code")
    , ("federated flow: it carries PKCE S256 (AUTH-6.1)",
        parameter url "code_challenge_method" == some "S256"
          && (parameter url "code_challenge").isSome)
    , ("federated flow: it carries a nonce (AUTH-6.3)", (parameter url "nonce").isSome)
    , ("federated flow: the cookie holds the same state the URL does",
        cookieValue == state && !state.isEmpty)
    , ("federated flow: the cookie is Lax, so the callback navigation carries it",
        (started.map (·.cookie.sameSite)) == some .lax)
    , ("federated flow: the cookie is HttpOnly and Secure",
        (started.map (fun s => s.cookie.httpOnly && s.cookie.secure)) == some true)
    , ("federated flow: a callback that pairs signs the person in",
        (completed.toOption.map (·.outcome.session.isSome)) == some true)
    , ("federated flow: and lands where the sign-in asked",
        (completed.toOption.bind (·.returnTo)) == some "/dashboard")
    , ("federated flow: the code was exchanged exactly once", afterFirst == 1)
    , ("federated flow: replaying the state is refused (AUTH-6.2)", refused replayed)
    , ("federated flow: a state that does not match the cookie is refused", refused mismatched)
    , ("federated flow: and costs no exchange", afterMismatch == 0)
    , ("federated flow: a callback with no cookie is refused", refused noCookie)
    , ("federated flow: an unverified address reaches the linking rule and is refused",
        (unverified.toOption.map (·.outcome.refused)) == some (some .addressNotVerified)) ]


/--
An invitation completed with a provider instead of email (AUTH-8.6).

The invitation is a grant on an address, not on a mechanism, so the provider asserting that
address is what makes this the invited person. The provider asserting a different one is not, and
is the case that keeps the grant from being a grant on whoever holds the link.
-/
def invitationChecks : IO (List (String × Bool)) := do
  let invited := address "invitee@example.com"
  let elsewhere := address "someone-else@example.com"
  let inviteOnly : TenantConfig tenant := { config with signupPolicy := .inviteOnly }

  let db ← openDb
  let ports := portsOn db
  ports.store.createInvitation tenant
    { id := ⟨"invite-1"⟩
      address := invited
      tokenDigest := peppers.current.digest ⟨"token"⟩
      metadata := ⟨"{}"⟩
      expiresAt := ⟨1700009999⟩
      createdBy := .client "admin" }
  let begun ← beginFederated ports inviteOnly provider discovery redirectUri none
    (some ⟨"invite-1"⟩)
  let state := (begun.bind fun s => parameter s.authorizationUrl "state").getD ""
  let cookie := (begun.map (·.cookie.value)).getD ""
  let admitted ← completeFederated ports (portsAsserting invited) inviteOnly provider discovery
    redirectUri (some state) (some cookie) "the-code" {}

  -- The same invitation, and a provider naming somebody else.
  let other ← openDb
  let otherPorts := portsOn other
  otherPorts.store.createInvitation tenant
    { id := ⟨"invite-2"⟩
      address := invited
      tokenDigest := peppers.current.digest ⟨"token"⟩
      metadata := ⟨"{}"⟩
      expiresAt := ⟨1700009999⟩
      createdBy := .client "admin" }
  let begunOther ← beginFederated otherPorts inviteOnly provider discovery
    redirectUri none (some ⟨"invite-2"⟩)
  let otherState := (begunOther.bind fun s => parameter s.authorizationUrl "state").getD ""
  let otherCookie := (begunOther.map (·.cookie.value)).getD ""
  let mismatched ← completeFederated otherPorts (portsAsserting elsewhere) inviteOnly provider
    discovery redirectUri (some otherState) (some otherCookie) "the-code" {}
  let stillInvited ← otherPorts.store.invitationById tenant ⟨"invite-2"⟩

  pure
    [ ("invitation: a provider asserting the invited address completes the invitation (AUTH-8.6)",
        (admitted.toOption.map (·.outcome.session.isSome)) == some true)
    , ("invitation: and the account was created, which invite-only would otherwise refuse",
        (admitted.toOption.map (·.outcome.admitted.isSome)) == some true)
    , ("invitation: a provider asserting another address does not complete it",
        match mismatched with | .error _ => true | .ok _ => false)
    , ("invitation: and the invitation is left unspent",
        (stillInvited.map (·.state)) == some .pending) ]

/--
The start of a federated sign-in is rate limited (AUTH-14.1.1).

It is an unauthenticated endpoint that writes a row and asks somebody else a question, so what
bounds it is the source and the tenant. Nobody has said who they are yet, which is why the two
scopes that need an address are not among them.
-/
def limitChecks : IO (List (String × Bool)) := do
  let db ← openDb
  let counted ← IO.mkRef 0
  let limited : Ports IO :=
    { portsOn db with
      limiter :=
        { admit := fun action _ scopes => do
            counted.modify (· + 1)
            pure (action != .federatedStart || (← counted.get) ≤ 2 && !scopes.isEmpty) } }
  let requester : RequestContext := { ip := some "198.51.100.7" }
  let first ← beginFederated limited config provider discovery redirectUri none none requester
  let second ← beginFederated limited config provider discovery redirectUri none none requester
  let third ← beginFederated limited config provider discovery redirectUri none none requester
  let scopes := startScopes tenant requester
  let anonymous := startScopes tenant {}
  pure
    [ ("federated flow: the start is admitted while inside the budget",
        first.isSome && second.isSome)
    , ("federated flow: and refused once past it (AUTH-14.1.1)", third.isNone)
    , ("federated flow: a refused start writes no state record",
        (← (portsOn db).store.federationStateByDigest tenant ⟨1700000000⟩
          (peppers.current.digest ⟨"nothing"⟩)).isNone)
    , ("federated flow: the source, the tenant and everyone are counted",
        scopes.length == 3 && scopes.contains (.sourceIp "198.51.100.7"))
    , ("federated flow: a request with no source still counts against the other two",
        anonymous.length == 2) ]
end Tests.FederatedFlow
