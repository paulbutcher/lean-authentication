/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import AuthenticationSqlite

/-!
Signup policy and invitations, run through the whole flow (§7, §8).

Policy is decided where the account is created, so nothing here can be checked by calling
`evaluate`; a check has to drive an attempt to completion and see whether an account came out.
That is also the point: a policy that is right in `evaluate` and never consulted looks identical
to one that works.
-/

namespace Tests.Signup
open Authentication Authentication.Service

initialize clockRef : IO.Ref Timestamp ← IO.mkRef ⟨1700000000⟩
initialize drawCounter : IO.Ref Nat ← IO.mkRef 0
initialize sentRef : IO.Ref (List OutboundEmail) ← IO.mkRef []

instance : Clock IO where
  now := clockRef.get

instance : RandomBytes IO where
  draw count := do
    let index ← drawCounter.modifyGet fun n => (n, n + 1)
    pure (.ok ((Crypto.Sha256.hashUtf8 s!"signup-seed-{index}").extract 0 count))

def capturing : EmailTransport IO where
  send mail := do
    sentRef.modify (· ++ [mail])
    pure (.ok ⟨mail.idempotencyKey⟩)

private def address (raw : String) : EmailAddress := (EmailAddress.parse raw).toOption.getD default

private def domain (raw : String) : Domain := (Domain.parse raw).toOption.getD ⟨[]⟩

def peppers : PepperRing :=
  { current := { keyId := ⟨"pepper-1"⟩, secret := Crypto.Sha256.hashUtf8 "test pepper" } }

private def portsOn (db : SQLite) : Ports IO :=
  { store := Sqlite.store db
    transport := capturing
    responsePolicy := SignInResponsePolicy.silent IO
    limiter := RateLimiter.unlimited IO
    responseFloor := ResponseFloor.immediate IO
    peppers }

private def configFor (tenant : TenantId) (policy : SignupPolicy)
    (invitationOverrides : Bool := true) : TenantConfig tenant :=
  { displayName := "Acme"
    baseUrl := ⟨"https://auth.example.com"⟩
    sendingIdentity :=
      { address := address "sign-in@auth.example.com", displayName := "Acme sign-in" }
    signupPolicy := policy
    invitationOverridesAllowlist := invitationOverrides }

private def parameterFrom (body : String) (name : String) : Option String :=
  let rest := (body.splitOn (name ++ "=")).drop 1
  rest[0]?.map fun tail =>
    String.ofList (tail.toList.takeWhile fun c => c != '&' && c != '\n' && c != ' ')

private def cookieNonce {tenant : TenantId} (outcome : Outcome tenant) : Option CredentialValue :=
  outcome.setCookies[0]?.bind fun cookie =>
    match cookie.value.splitOn ":" with
    | [_, nonce] => some ⟨nonce⟩
    | _ => none

/-- Drives an attempt that has already been begun all the way to a session, the way a person
would: read the link out of the mail, open it on another device, type the code back. -/
private def finish {tenant : TenantId} (ports : Ports IO) (config : TenantConfig tenant)
    (begun : Outcome tenant) (mailIndex : Nat) : IO (Except AuthError (Outcome tenant)) := do
  let body := (((← sentRef.get)[mailIndex]?).map (·.textBody)).getD ""
  let attempt : AttemptId tenant := ⟨(parameterFrom body "attempt").getD ""⟩
  let token : CredentialValue := ⟨(parameterFrom body "token").getD ""⟩
  let _ ← openLink ports config attempt token none
  let typed := displayCode (revealedCode ports.peppers token)
  match cookieNonce begun with
  | some nonce => submitCode ports config attempt typed nonce {}
  | none => pure (.error .notOriginatingBrowser)

private def viewsOf {t : TenantId} (result : Except AuthError (Outcome t)) : List View :=
  match result with
  | .ok outcome => outcome.views
  | .error _ => []

private def sessionOf {t : TenantId} (result : Except AuthError (Outcome t)) :
    Option CredentialValue :=
  match result with
  | .ok outcome => outcome.session
  | .error _ => none

private def admittedOf {t : TenantId} (result : Except AuthError (Outcome t)) :
    Option (AccountAdmitted t) :=
  match result with
  | .ok outcome => outcome.admitted
  | .error _ => none

private def errorOf {t : TenantId} (result : Except AuthError (Outcome t)) : Option AuthError :=
  match result with
  | .ok _ => none
  | .error e => some e

/-- Only the identifier and the token are needed downstream, so nothing here needs a default
`Invitation`, which is not a value this library should have lying around. -/
private def issuedIds {t : TenantId} (created : Option (Invitation t × CredentialValue)) :
    InvitationId t × CredentialValue :=
  match created with
  | some (invitation, token) => (invitation.id, token)
  | none => (⟨""⟩, ⟨""⟩)

/-- One sign-in from nothing, under whatever policy the tenant has. -/
private def signInUnder (tenant : TenantId) (policy : SignupPolicy) (raw : String) :
    IO (Except AuthError (Outcome tenant)) := do
  sentRef.set []
  let db ← Sqlite.openInMemory
  let ports := portsOn db
  let config := configFor tenant policy
  let (begun, _) ← begin ports config (address raw) {}
  finish ports config begun 0

def checks : IO (List (String × Bool)) := do
  let allowlist : SignupPolicy := .domainAllowlist [domain "example.com"] false

  let unrestricted ← signInUnder ⟨"s-open"⟩ .unrestricted "person@example.com"
  let allowed ← signInUnder ⟨"s-allow"⟩ allowlist "person@example.com"
  let refused ← signInUnder ⟨"s-refuse"⟩ allowlist "person@evilexample.com"
  let uninvited ← signInUnder ⟨"s-invite"⟩ .inviteOnly "person@example.com"

  -- The true reason is audited even though the person is shown a policy refusal.
  let auditOfRefusal ← do
    let db ← Sqlite.openInMemory
    let ports := portsOn db
    let tenant : TenantId := ⟨"s-audit"⟩
    let config := configFor tenant .inviteOnly
    sentRef.set []
    let (begun, _) ← begin ports config (address "person@example.com") {}
    let _ ← finish ports config begun 0
    pure (← ports.store.auditEntries tenant)

  pure
    [ ("signup: an unrestricted tenant admits any well-formed address",
        (sessionOf unrestricted).isSome && (admittedOf unrestricted).isSome),
      ("signup: the first account in a tenant is reported as the first (AUTH-13.6)",
        (admittedOf unrestricted).map (·.firstInTenant) == some true),
      ("signup: an allowed domain is admitted",
        (sessionOf allowed).isSome),
      ("signup: a domain that is a suffix without a label boundary is refused (AUTH-7.3.1)",
        (sessionOf refused).isNone
          && viewsOf refused == [.signupRefused .domainNotAllowed]),
      ("signup: invite-only refuses an address with no invitation",
        (sessionOf uninvited).isNone
          && viewsOf uninvited == [.signupRefused .notInvited]),
      ("signup: a refusal is audited with its true reason (AUTH-7.7)",
        auditOfRefusal.any fun entry =>
          match entry.event with
          | .signInRejected .notInvited => true
          | _ => false) ]

/-! ## Invitations -/

private def metadata : InvitationMetadata := ⟨"{\"role\":\"editor\"}"⟩

def invitationChecks : IO (List (String × Bool)) := do
  let tenant : TenantId := ⟨"s-inv"⟩
  let db ← Sqlite.openInMemory
  let ports := portsOn db
  let config := configFor tenant .inviteOnly
  sentRef.set []

  let created ← createInvitation ports config (address "guest@elsewhere.com") metadata
  let invitationMail := (← sentRef.get)[0]?
  let (invitationId, token) := issuedIds created

  -- Accepting begins an attempt for the invited address and mails a sign-in link.
  let accepted ← acceptInvitation ports config invitationId token {}
  let signedIn ← match accepted with
    | .ok begun => finish ports config begun 1
    | .error _ => pure (.error .invitationNotPending)

  let listed ← invitations (tenant := tenant) ports
  let replay ← acceptInvitation ports config invitationId token {}

  -- A second invitation, to check revocation and rotation on a fresh record.
  let second ← createInvitation ports config (address "other@elsewhere.com") metadata
  let (secondInvitationId, secondToken) := issuedIds second
  let rotated ← resendInvitation ports config secondInvitationId
  let staleAccept ← acceptInvitation ports config secondInvitationId secondToken {}
  let freshAccept ← acceptInvitation ports config secondInvitationId (rotated.getD ⟨""⟩) {}

  let third ← createInvitation ports config (address "third@elsewhere.com") metadata
  let (thirdInvitationId, thirdToken) := issuedIds third
  let revoked ← revokeInvitation ports thirdInvitationId
  let revokedAccept ← acceptInvitation ports config thirdInvitationId thirdToken {}

  pure
    [ ("invitation: creating one mails the invited address",
        (invitationMail.map (·.to.render)) == some "guest@elsewhere.com"),
      ("invitation: the mail carries an accept link, not a sign-in link",
        (((invitationMail.map (·.textBody)).getD "").splitOn "/invitation/accept").length == 2),
      ("invitation: accepting sends a sign-in mail rather than signing in on the spot",
        (← sentRef.get).length ≥ 2 && (sessionOf accepted).isNone),
      ("invitation: the flow completes and an account is created for the invited address",
        (sessionOf signedIn).isSome && (admittedOf signedIn).isSome),
      ("invitation: the metadata is handed back unread (AUTH-8.7)",
        (admittedOf signedIn).bind (·.invitationMetadata) == some metadata),
      ("invitation: an invitation admits an address the policy would refuse (AUTH-7.5)",
        (sessionOf signedIn).isSome),
      ("invitation: it is single use (AUTH-8.5)",
        errorOf replay == some .invitationNotPending),
      ("invitation: listing reports what happened to each (AUTH-8.9)",
        (listed.find? fun (i, _) => i.id == invitationId).map (·.2) == some .accepted),
      ("invitation: resending rotates the token and invalidates the old one (AUTH-8.5)",
        rotated.isSome && rotated != some secondToken
          && errorOf staleAccept == some .unknownToken && (errorOf freshAccept).isNone),
      ("invitation: a revoked invitation cannot be accepted",
        revoked && errorOf revokedAccept == some .invitationNotPending) ]

/-- AUTH-8.8: an invitation for an address that already has an account signs that account in and
is consumed, rather than creating a second account. -/
def existingAccountChecks : IO (List (String × Bool)) := do
  let tenant : TenantId := ⟨"s-dup"⟩
  let db ← Sqlite.openInMemory
  let ports := portsOn db
  let config := configFor tenant .unrestricted
  sentRef.set []

  let person := address "person@example.com"
  let (begun, _) ← begin ports config person {}
  let first ← finish ports config begun 0

  let created ← createInvitation ports config person metadata
  let (invitationId, token) := issuedIds created
  let accepted ← acceptInvitation ports config invitationId token {}
  let second ← match accepted with
    | .ok begunAgain => finish ports config begunAgain 2
    | .error _ => pure (.error .invitationNotPending)

  let firstAccount ← match sessionOf first with
    | some credential => identify (tenant := tenant) ports credential
    | none => pure none
  let secondAccount ← match sessionOf second with
    | some credential => identify (tenant := tenant) ports credential
    | none => pure none
  let listed ← invitations (tenant := tenant) ports

  pure
    [ ("invitation: accepting for an existing account signs that account in (AUTH-8.8)",
        firstAccount.isSome && secondAccount.isSome
          && firstAccount.map (·.account.value) == secondAccount.map (·.account.value)),
      ("invitation: no second account is created for the same address",
        (admittedOf second).isNone),
      ("invitation: the invitation is consumed all the same (AUTH-8.8)",
        (listed.find? fun (i, _) => i.id == invitationId).map (·.2) == some .accepted) ]

end Tests.Signup
