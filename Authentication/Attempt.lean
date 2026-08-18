/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Authentication.Account
import Authentication.Audit
import Authentication.Config
import Authentication.Digest
import Authentication.Email
import Authentication.Error
import Authentication.Invitation

/-!
The magic link flow as a pure function over an explicit state (AUTH-3.1, §5).

Nothing here performs an effect. Time and the digests of whatever a request offered arrive as
arguments, and everything the edge must do afterwards comes back as data.
-/

namespace Authentication

inductive AttemptPhase where
  | pending
  | revealed
  | completed
  | expired
  | abandoned
  deriving DecidableEq, Repr, Inhabited

def AttemptPhase.isLive : AttemptPhase → Bool
  | .pending | .revealed => true
  | .completed | .expired | .abandoned => false

/-- One sign-in in progress (AUTH-4.4.3). Every credential is held as a digest. -/
structure AttemptState (tenant : TenantId) where
  id : AttemptId tenant
  address : EmailAddress
  phase : AttemptPhase
  magicToken : Digest
  revealedCode : Digest
  emailedCode : Option Digest
  bindingNonce : Digest
  failedCodeEntries : Nat
  expiresAt : Timestamp
  requester : RequestContext
  /-- The invitation this attempt is accepting, if it is one. Carried on the attempt rather than
  supplied at completion, so the address an acceptance creates an account for comes from the
  invitation record and from nowhere else (AUTH-8.3). -/
  invitation : Option (InvitationId tenant) := none
  deriving DecidableEq, Repr

inductive AttemptEvent where
  | linkOpened (token : PresentedSecret) (cookie : Option PresentedSecret)
  | completionRequested (cookie : PresentedSecret)
  | revealedCodeSubmitted (cookie : PresentedSecret) (code : PresentedSecret)
  | emailedCodeSubmitted (cookie : PresentedSecret) (code : PresentedSecret)
  | superseded
  deriving Repr

inductive View where
  | mailSent
  | confirmSignIn
  | showVerificationCode
  | codeRejected (remaining : Nat)
  | signedIn
  /-- The address was proven and still no session was issued. Emitted by the service rather than
  by `step`, because both reasons are decided where the account is reached (AUTH-7.6). -/
  | refused (reason : SignInRefusal)
  deriving DecidableEq, Repr, Inhabited

/-- What the mailer is given. No field can carry anything the requester typed, which is how
AUTH-5.2.12's last sentence is kept: there is nowhere to put it. -/
structure SignInEmail (tenant : TenantId) where
  attempt : AttemptId tenant
  recipient : EmailAddress
  magicLink : Url
  emailedCode : Option CredentialValue
  requester : RequestContext
  requestedAt : Timestamp
  deriving DecidableEq, Repr

structure SessionSubject (tenant : TenantId) where
  attempt : AttemptId tenant
  address : EmailAddress
  invitation : Option (InvitationId tenant) := none
  /-- The browser the flow began in, which is the one the session is issued to: every completion
  path checks the binding nonce, so no other browser can reach this point. It is what a session
  listing shows the account holder about the session (AUTH-9.5). -/
  requester : RequestContext
  deriving DecidableEq, Repr

inductive Effect (tenant : TenantId) where
  | audit (entry : AuditEntry tenant)
  | sendSignInEmail (message : SignInEmail tenant)
  | setAttemptCookie (cookie : CookieSpec)
  | clearAttemptCookie (name : String) (path : String)
  | issueSession (subject : SessionSubject tenant)
  | present (view : View)
  deriving DecidableEq, Repr

/-- The credentials an attempt needs, minted at the edge where the randomness and the pepper
live. -/
structure MintedSecrets where
  magicToken : MintedCredential
  /-- Derived from the magic token rather than drawn independently. The landing page has to
  show the same code however often the link is opened (AUTH-5.2.2), and no stored record may
  hold a credential in clear (AUTH-5.3.4), so the token that opened the link is the only thing
  the code can be recovered from. -/
  revealedCode : MintedCredential
  emailedCode : Option MintedCredential
  bindingNonce : MintedCredential

namespace Attempt

def magicLink {tenant : TenantId} (config : TenantConfig tenant) (attempt : AttemptId tenant)
    (token : CredentialValue) : Url :=
  config.baseUrl.url tenant ("/signin/link?attempt=" ++ attempt.value ++ "&token=" ++ token.encoded)

/-- The cookie names the attempt and carries the nonce it is checked against, so holding an
attempt id is not enough to be taken for the browser that started the flow (AUTH-5.2.5). -/
def cookieValue {tenant : TenantId} (attempt : AttemptId tenant) (nonce : CredentialValue) :
    String :=
  attempt.value ++ ":" ++ nonce.encoded

def begin {tenant : TenantId} (config : TenantConfig tenant) (now : Timestamp)
    (attempt : AttemptId tenant) (address : EmailAddress) (secrets : MintedSecrets)
    (requester : RequestContext) (invitation : Option (InvitationId tenant) := none) :
    AttemptState tenant × List (Effect tenant) :=
  let expiresAt := now.advance config.attemptLifetime.duration
  let state : AttemptState tenant :=
    { id := attempt
      address
      phase := .pending
      magicToken := secrets.magicToken.digest
      revealedCode := secrets.revealedCode.digest
      emailedCode := secrets.emailedCode.map (·.digest)
      bindingNonce := secrets.bindingNonce.digest
      failedCodeEntries := 0
      expiresAt
      requester
      invitation }
  (state,
    [ .audit ⟨now, .anonymous, .attemptCreated attempt⟩,
      .setAttemptCookie
        (CookieSpec.forAttempt tenant (cookieValue attempt secrets.bindingNonce.value) expiresAt),
      .sendSignInEmail
        { attempt
          recipient := address
          magicLink := magicLink config attempt secrets.magicToken.value
          emailedCode := secrets.emailedCode.map (·.value)
          requester
          requestedAt := now },
      .present .mailSent ])

private def complete {tenant : TenantId} (now : Timestamp) (state : AttemptState tenant) :
    AttemptState tenant × List (Effect tenant) :=
  ({ state with phase := .completed },
    [ .audit ⟨now, .anonymous, .sessionIssued state.id⟩,
      .issueSession ⟨state.id, state.address, state.invitation, state.requester⟩,
      .clearAttemptCookie "auth_attempt" (BaseUrl.tenantPath tenant),
      .present .signedIn ])

/-- The entry budget is shared by both codes (AUTH-5.4.2), and is checked before the code is,
so the sixth entry abandons the attempt whatever it was (AUTH-5.2.7). -/
private def submitCode {tenant : TenantId} (config : TenantConfig tenant) (now : Timestamp)
    (state : AttemptState tenant) (cookie code : PresentedSecret) (stored : Digest) :
    Except AuthError (AttemptState tenant × List (Effect tenant)) :=
  if !state.bindingNonce.accepts cookie then .error .notOriginatingBrowser
  else if config.maxCodeEntries ≤ state.failedCodeEntries then
    .ok ({ state with phase := .abandoned },
      [ .audit ⟨now, .anonymous, .codeEntered state.id .budgetExhausted⟩,
        .audit ⟨now, .anonymous, .attemptAbandoned state.id .codeBudgetExhausted⟩,
        .present (.codeRejected 0) ])
  else if stored.accepts code then
    let (next, effects) := complete now state
    .ok (next, .audit ⟨now, .anonymous, .codeEntered state.id .accepted⟩ :: effects)
  else
    .ok ({ state with failedCodeEntries := state.failedCodeEntries + 1 },
      [ .audit ⟨now, .anonymous, .codeEntered state.id .rejected⟩,
        .present (.codeRejected (config.maxCodeEntries - state.failedCodeEntries - 1)) ])

/--
Expiry is decided here rather than trusted from the stored phase, so a `pending` record whose
time has passed cannot be completed by a caller that has not swept it (AUTH-5.2.8,
AUTH-15.4.3).
-/
def step {tenant : TenantId} (config : TenantConfig tenant) (now : Timestamp)
    (state : AttemptState tenant) (event : AttemptEvent) :
    Except AuthError (AttemptState tenant × List (Effect tenant)) :=
  if !state.phase.isLive then .error .attemptNotLive
  else if state.expiresAt ≤ now then .error .attemptExpired
  else
    match event with
    | .superseded =>
      .ok ({ state with phase := .abandoned },
        [.audit ⟨now, .anonymous, .attemptAbandoned state.id .superseded⟩])
    | .linkOpened token cookie =>
      -- A `GET`: it issues nothing and consumes nothing, so a link scanner cannot spend the
      -- attempt, and opening the link again shows the same page (AUTH-5.2.1, AUTH-5.2.2).
      if !state.magicToken.accepts token then .error .unknownToken
      else
        -- The cookie alone decides the device. User agents, addresses and fingerprints are
        -- unreliable and their failure mode is locking people out (AUTH-5.2.3).
        let device :=
          match cookie with
          | some presented => if state.bindingNonce.accepts presented then Device.same
            else Device.cross
          | none => Device.cross
        .ok ({ state with phase := .revealed },
          [ .audit ⟨now, .anonymous, .linkOpened state.id device⟩,
            .present (match device with
              | .same => .confirmSignIn
              | .cross => .showVerificationCode) ])
    | .completionRequested cookie =>
      if state.phase != .revealed then .error .codeNotYetAvailable
      else if !state.bindingNonce.accepts cookie then .error .notOriginatingBrowser
      else .ok (complete now state)
    | .revealedCodeSubmitted cookie code =>
      if state.phase != .revealed then .error .codeNotYetAvailable
      else submitCode config now state cookie code state.revealedCode
    | .emailedCodeSubmitted cookie code =>
      -- Admitted while the attempt is still `pending`, unlike the revealed code. It reaches
      -- the person in the mail itself, for whom the point is not having to open the link at
      -- all (AUTH-5.4.1); requiring `revealed` would leave it with no use.
      match state.emailedCode with
      | none => .error .emailedCodeNotEnabled
      | some stored => submitCode config now state cookie code stored

end Attempt

end Authentication
