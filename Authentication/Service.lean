/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Authentication.Attempt
import Authentication.Pepper
import Authentication.Port.Clock
import Authentication.Port.Email
import Authentication.Port.Latency
import Authentication.Port.RateLimiter
import Authentication.Response
import Authentication.Store
import Codec.Base32
import Codec.Base64Url

/-!
The interpreter at the edge (AUTH-3.1).

Every decision about the sign-in flow is taken by `Attempt.step`; this module mints credentials,
reads and writes through the store, and performs the effects the state machine asked for.

The one decision taken here is signup policy, because AUTH-7.6 evaluates it at account creation
and account creation is here. Deciding it at `begin` would be worse than misplaced: it would
tell an unauthenticated caller whether an address may sign up, which is what AUTH-14.2 exists to
prevent. By the time `issueSession` runs, whoever is asking has proven control of the address.
-/

namespace Authentication.Service

open Codec

/-- The implementations chosen at startup (AUTH-3.5), together with the peppers in force. -/
structure Ports (m : Type → Type) where
  store : AuthStore m
  transport : EmailTransport m
  responsePolicy : SignInResponsePolicy m
  limiter : RateLimiter m
  responseFloor : ResponseFloor m
  peppers : PepperRing

/--
What an account creation tells the client. Both fields exist because the library owns identity
and nothing else (§13): with no roles here, `firstInTenant` is the only thing that can make a
tenant's first account privileged (AUTH-13.6), and the metadata is the client's own payload
handed back unread (AUTH-8.7, AUTH-13.3).
-/
structure AccountAdmitted (tenant : TenantId) where
  account : AccountId tenant
  firstInTenant : Bool
  invitationMetadata : Option InvitationMetadata := none
  deriving DecidableEq, Repr

/-- What the caller has to act on: the pages to show, the cookies to set, and the session
credential, if one was issued. The HTTP layer that turns these into a response arrives with the
integration target. -/
structure Outcome (tenant : TenantId) where
  views : List View := []
  setCookies : List CookieSpec := []
  clearCookies : List (String × String) := []
  session : Option CredentialValue := none
  sent : List SentMessageId := []
  /-- Present only when this outcome created an account, not on every sign-in. -/
  admitted : Option (AccountAdmitted tenant) := none
  refused : Option SignupRejection := none
  deriving Inhabited

private def randomValue {m : Type → Type} [Monad m] [RandomBytes m] (bytes : Nat) :
    m (Except String CredentialValue) := do
  match ← RandomBytes.draw bytes with
  | .error e => pure (.error e)
  | .ok drawn => pure (.ok ⟨Base64Url.encodeString drawn⟩)

/-- The code the cross-device landing page shows: at least 40 bits, in an alphabet with no
confusable pair, and grouped for transcription (AUTH-5.3.2). It is derived from the token that
opened the link, which is why it can be shown again without ever having been stored
(AUTH-5.2.2). -/
def revealedCode (peppers : PepperRing) (token : CredentialValue) : CredentialValue :=
  ⟨Base32.encodeString ((peppers.current.derive "revealed-code" token).extract 0 5)⟩

/-- The grouping is for the eye and the typing hand only. What is digested is the canonical
form, so a code typed back with or without the grouping is the same code. -/
def displayCode (code : CredentialValue) : String :=
  String.ofList (code.encoded.toList.take 4) ++ "-" ++ String.ofList (code.encoded.toList.drop 4)

/-- Accepts a code as it was transcribed, then digests the canonical form of it. This is what
makes the Crockford substitutions reachable: a person who typed `O` for `0`, dropped the
grouping hyphen, or used lower case has still typed the code. -/
def canonicalCode (typed : String) : Option CredentialValue :=
  (Base32.decodeString typed).map fun bytes => ⟨Base32.encodeString bytes⟩

private def emailedCodeOf (drawn : ByteArray) : CredentialValue :=
  let value := drawn.toList.foldl (fun acc byte => acc * 256 + byte.toNat) 0 % 1000000
  let digits := toString value
  ⟨String.ofList (List.replicate (6 - digits.length) '0') ++ digits⟩

def mintSecrets {m : Type → Type} [Monad m] [RandomBytes m] {tenant : TenantId}
    (peppers : PepperRing) (config : TenantConfig tenant) :
    m (Except String MintedSecrets) := do
  match ← randomValue 16, ← randomValue 16 with
  | .error e, _ => pure (.error e)
  | _, .error e => pure (.error e)
  | .ok token, .ok nonce =>
    let code := revealedCode peppers token
    let emailed : Except String (Option MintedCredential) ←
      if config.emailedCodeEnabled then
        match ← RandomBytes.draw 4 with
        | .error e => pure (.error e)
        | .ok drawn =>
          let value := emailedCodeOf drawn
          pure (.ok (some { value, digest := peppers.current.digest value }))
      else pure (.ok none)
    match emailed with
    | .error e => pure (.error e)
    | .ok emailedCode =>
      pure (.ok
        { magicToken := { value := token, digest := peppers.current.digest token }
          revealedCode := { value := code, digest := peppers.current.digest code }
          emailedCode
          bindingNonce := { value := nonce, digest := peppers.current.digest nonce } })

/-- The mail states the tenant, the time, and where the request came from, and carries nothing
the requester typed (AUTH-5.2.11, AUTH-5.2.12). What it says is the tenant's template's business
(AUTH-10.7); what it is addressed from, and the key that makes a retry safe, are not. -/
private def signInEmail {tenant : TenantId} (config : TenantConfig tenant)
    (message : SignInEmail tenant) : OutboundEmail :=
  let rendered := config.templates.signIn
    { tenantName := config.displayName
      recipient := message.recipient
      magicLink := message.magicLink.value
      emailedCode := message.emailedCode.map (·.encoded)
      requester := message.requester
      requestedAt := message.requestedAt }
  { «from» := config.sendingIdentity
    to := message.recipient
    subject := rendered.subject
    textBody := rendered.textBody
    htmlBody := rendered.htmlBody
    replyTo := config.sendingIdentity.replyTo
    idempotencyKey := s!"attempt:{message.attempt.value}" }

/-- What issuing produced, so that a refusal can be told apart from a failure to draw random
bytes, and so the client learns about an account only when one was made. -/
private structure Issued (tenant : TenantId) where
  session : Option CredentialValue := none
  admitted : Option (AccountAdmitted tenant) := none
  refused : Option SignupRejection := none

/-- Spends the invitation the attempt was begun with, under compare-and-set so that two requests
racing to accept one invitation produce one account (AUTH-8.5). Returns what it granted; a
grant that loses the race grants nothing. -/
private def spendInvitation {m : Type → Type} [Monad m] {tenant : TenantId} (ports : Ports m)
    (now : Timestamp) (id : InvitationId tenant) : m (Option (InvitationGrant tenant)) := do
  match ← ports.store.invitationById tenant id with
  | none => pure none
  | some invitation =>
    if invitation.state != .pending then pure none
    else if invitation.expiresAt ≤ now then pure none
    else if ← ports.store.commitInvitation tenant invitation (Invitation.markConsumed now invitation) then
      ports.store.appendAudit tenant ⟨now, .anonymous, .invitationConsumed id⟩
      pure (some
        { invitation := id, address := invitation.address, metadata := invitation.metadata })
    else pure none

private def issueSession {m : Type → Type} [Monad m] [RandomBytes m] {tenant : TenantId}
    (ports : Ports m) (config : TenantConfig tenant) (now : Timestamp)
    (subject : SessionSubject tenant) : m (Issued tenant) := do
  let identity := subject.address.normalise
  let existing ← ports.store.accountByIdentity tenant identity
  -- The invitation is spent whether or not an account had to be created, because AUTH-8.8 says
  -- an invitation for an address that already has an account signs that account in and is
  -- consumed, rather than creating a duplicate.
  let grant ← match subject.invitation with
    | some id => spendInvitation ports now id
    | none => pure none
  let (accountId, admitted, refused) ←
    match existing with
    | some account =>
      -- Policy is evaluated at account creation only, so tightening one never locks out an
      -- account that already exists (AUTH-7.6).
      pure (some account.id, none, none)
    | none =>
      match config.signupPolicy.evaluate subject.address grant.isSome
          config.invitationOverridesAllowlist with
      | .rejected reason => pure (none, none, some reason)
      | .permitted =>
        match ← randomValue 12 with
        | .error _ => pure (none, none, none)
        | .ok generated =>
          let account : Account tenant :=
            { id := ⟨generated.encoded⟩
              identity
              primaryEmail := subject.address
              createdAt := now }
          match ← ports.store.createAccount tenant account with
          | .ok created =>
            pure (some created.account.id,
              some { account := created.account.id
                     firstInTenant := created.firstInTenant
                     invitationMetadata := grant.map (·.metadata) },
              none)
          | .error _ =>
            pure ((← ports.store.accountByIdentity tenant identity).map (·.id), none, none)
  match accountId with
  | none =>
    -- The true reason is recorded whatever the person is shown (AUTH-7.7).
    match refused with
    | some reason =>
      ports.store.appendAudit tenant ⟨now, .anonymous,
        .signInRejected (match reason with
          | .notInvited => .notInvited
          | .domainNotAllowed => .domainNotAllowed)⟩
      pure { refused }
    | none => pure {}
  | some accountId =>
    match ← randomValue 16 with
    | .error _ => pure { admitted }
    | .ok credential =>
      -- A new identifier at every sign-in; an existing session is never promoted (AUTH-9.3).
      ports.store.createSession tenant
        { id := ⟨credential.encoded⟩
          account := accountId
          identifierDigest := ports.peppers.current.digest credential
          createdAt := now
          lastSeenAt := now
          idleExpiresAt := now.advance config.sessionIdleTimeout
          absoluteExpiresAt := now.advance config.sessionAbsoluteLifetime }
      pure { session := some credential, admitted }

private def perform {m : Type → Type} [Monad m] [RandomBytes m] {tenant : TenantId}
    (ports : Ports m) (config : TenantConfig tenant) (now : Timestamp)
    (outcome : Outcome tenant) : Effect tenant → m (Outcome tenant)
  | .audit entry => do
    ports.store.appendAudit tenant entry
    pure outcome
  | .sendSignInEmail message => do
    match ← ports.transport.send (signInEmail config message) with
    | .ok id => pure { outcome with sent := outcome.sent ++ [id] }
    | .error _ => pure outcome
  | .setAttemptCookie cookie => pure { outcome with setCookies := outcome.setCookies ++ [cookie] }
  | .clearAttemptCookie name path =>
    pure { outcome with clearCookies := outcome.clearCookies ++ [(name, path)] }
  | .issueSession subject => do
    let issued ← issueSession ports config now subject
    pure
      { outcome with
        session := issued.session
        admitted := issued.admitted
        refused := issued.refused }
  | .present view => pure { outcome with views := outcome.views ++ [view] }

/-- A refusal arrives after the state machine has already asked for `signedIn` to be shown,
because the state machine does not know about policy. Rather than teach it, the view it asked
for is replaced here, in the one place that knows the account was not made. -/
private def settle {tenant : TenantId} (outcome : Outcome tenant) : Outcome tenant :=
  match outcome.refused with
  | none => outcome
  | some reason =>
    { outcome with
      views := outcome.views.filter (· != .signedIn) ++ [.signupRefused reason]
      session := none }

private def performAll {m : Type → Type} [Monad m] [RandomBytes m] {tenant : TenantId}
    (ports : Ports m) (config : TenantConfig tenant) (now : Timestamp)
    (effects : List (Effect tenant)) : m (Outcome tenant) :=
  settle <$> effects.foldlM (fun outcome effect => perform ports config now outcome effect) {}

/--
The five scopes of AUTH-14.1.1, for one address and one request. The address scope is not tenant
qualified, which is the whole of its point: without it an attacker spraying one address across
many tenants multiplies the budget by the tenant count.

A request with no source address contributes to the other four rather than being waved through;
an absent IP is a proxy that did not say, not a caller who did nothing.
-/
def limitScopes (tenant : TenantId) (address : EmailAddress) (requester : RequestContext) :
    List LimitScope :=
  let normalised := address.normalise
  [ .tenantAddress tenant normalised, .address normalised, .tenant tenant, .global ]
    ++ (match requester.ip with | some ip => [.sourceIp ip] | none => [])

/--
Begins a sign-in. The response comes from the policy rather than from what happened, and every
outcome takes the same path through this function, so what the client chose to say cannot be
undone by a difference in shape (AUTH-14.2).
-/
def begin {m : Type → Type} [Monad m] [Clock m] [RandomBytes m] {tenant : TenantId}
    (ports : Ports m) (config : TenantConfig tenant) (address : EmailAddress)
    (requester : RequestContext) : m (Outcome tenant × SignInResponse) :=
  -- Every outcome leaves through the same floor, including the ones that did no work at all.
  ports.responseFloor.normalise do
  let now ← Clock.now
  if !(← ports.limiter.admit .send now (limitScopes tenant address requester)) then
    -- The true outcome is recorded whatever the person was told (AUTH-14.2.6), and the policy
    -- chooses only what is said: it cannot decline to be limited (AUTH-14.2.5).
    ports.store.appendAudit tenant ⟨now, .anonymous, .signInRejected .throttled⟩
    let response ← ports.responsePolicy.respond tenant .throttled
    return ({}, response)
  match ← mintSecrets ports.peppers config with
  | .error _ =>
    let response ← ports.responsePolicy.respond tenant .throttled
    pure ({}, response)
  | .ok secrets =>
    match ← randomValue 12 with
    | .error _ =>
      let response ← ports.responsePolicy.respond tenant .throttled
      pure ({}, response)
    | .ok generated =>
      let attemptId : AttemptId tenant := ⟨generated.encoded⟩
      let (state, effects) := Attempt.begin config now attemptId address secrets requester
      let superseded ← ports.store.startAttempt tenant state
      for abandoned in superseded do
        ports.store.appendAudit tenant
          ⟨now, .anonymous, .attemptAbandoned abandoned .superseded⟩
      let outcome ← performAll ports config now effects
      let response ← ports.responsePolicy.respond tenant .linkSent
      pure (outcome, response)

/-- Feeds one event to the state machine and, if it was accepted, writes the new state back
under compare-and-set before performing anything. A commit that lost changes nothing and
performs nothing. -/
private def advance {m : Type → Type} [Monad m] [Clock m] [RandomBytes m] {tenant : TenantId}
    (ports : Ports m) (config : TenantConfig tenant) (attempt : AttemptId tenant)
    (submission : Option RequestContext) (event : AttemptEvent) :
    m (Except AuthError (Outcome tenant)) := do
  let now ← Clock.now
  match ← ports.store.attemptById tenant attempt with
  | none => pure (.error .attemptNotLive)
  | some state =>
    -- The attempt is read before the limit is applied, because the address the budget belongs to
    -- is on the attempt and the caller supplied only an id. One indexed read ahead of the check
    -- is the price of not letting a caller choose which budget it is charged to.
    let permitted ← match submission with
      | none => pure true
      | some requester =>
        ports.limiter.admit .codeSubmission now (limitScopes tenant state.address requester)
    if !permitted then
      ports.store.appendAudit tenant ⟨now, .anonymous, .signInRejected .throttled⟩
      return .error .throttled
    match Attempt.step config now state event with
    | .error e => pure (.error e)
    | .ok (next, effects) =>
      if ← ports.store.commitAttempt tenant state next then
        .ok <$> performAll ports config now effects
      else
        pure (.error .attemptNotLive)

/-- Opening the magic link. A `GET` that issues nothing and consumes nothing (AUTH-5.2.1). -/
def openLink {m : Type → Type} [Monad m] [Clock m] [RandomBytes m] {tenant : TenantId}
    (ports : Ports m) (config : TenantConfig tenant) (attempt : AttemptId tenant)
    (token : CredentialValue) (cookie : Option CredentialValue) :
    m (Except AuthError (Outcome tenant)) :=
  advance ports config attempt none
    (.linkOpened (ports.peppers.present token) (cookie.map ports.peppers.present))

/-- The `POST` from the same-device landing page (AUTH-5.2.1). -/
def confirmSignIn {m : Type → Type} [Monad m] [Clock m] [RandomBytes m] {tenant : TenantId}
    (ports : Ports m) (config : TenantConfig tenant) (attempt : AttemptId tenant)
    (cookie : CredentialValue) : m (Except AuthError (Outcome tenant)) :=
  advance ports config attempt none (.completionRequested (ports.peppers.present cookie))

/-- The code typed into the browser the flow began in. -/
def submitCode {m : Type → Type} [Monad m] [Clock m] [RandomBytes m] {tenant : TenantId}
    (ports : Ports m) (config : TenantConfig tenant) (attempt : AttemptId tenant)
    (typed : String) (cookie : CredentialValue) (requester : RequestContext) :
    m (Except AuthError (Outcome tenant)) :=
  match canonicalCode typed with
  | none => pure (.error .notOriginatingBrowser)
  | some code =>
    advance ports config attempt (some requester)
      (.revealedCodeSubmitted (ports.peppers.present cookie) (ports.peppers.present code))

/-- The optional typed code from the mail body (AUTH-5.4). -/
def submitEmailedCode {m : Type → Type} [Monad m] [Clock m] [RandomBytes m] {tenant : TenantId}
    (ports : Ports m) (config : TenantConfig tenant) (attempt : AttemptId tenant)
    (typed : String) (cookie : CredentialValue) (requester : RequestContext) :
    m (Except AuthError (Outcome tenant)) :=
  advance ports config attempt (some requester)
    (.emailedCodeSubmitted (ports.peppers.present cookie) (ports.peppers.present ⟨typed⟩))

/-! ## Invitations

None of these check a permission, and that is the design rather than an omission. The library
owns identity and nothing about authorisation, so it has no basis on which to decide who may
invite; the client calls them only when it has decided (AUTH-13.2).
-/

def acceptLink {tenant : TenantId} (config : TenantConfig tenant) (invitation : InvitationId tenant)
    (token : CredentialValue) : Url :=
  config.baseUrl.url tenant
    ("/invitation/accept?invitation=" ++ invitation.value ++ "&token=" ++ token.encoded)

private def invitationEmail {tenant : TenantId} (config : TenantConfig tenant)
    (invitation : Invitation tenant) (link : Url) : OutboundEmail :=
  let rendered := config.templates.invitation
    { tenantName := config.displayName
      recipient := invitation.address
      acceptLink := link.value
      expiresAt := invitation.expiresAt }
  { «from» := config.sendingIdentity
    to := invitation.address
    subject := rendered.subject
    textBody := rendered.textBody
    htmlBody := rendered.htmlBody
    replyTo := config.sendingIdentity.replyTo
    -- The token rather than the invitation, so that a resend is a different message: AUTH-8.5
    -- rotates the token, and suppressing the second send as a duplicate would strand the person
    -- with a link that no longer works.
    idempotencyKey := s!"invitation:{invitation.id.value}:{invitation.tokenDigest.bytes.size}" }

/-- Creates an invitation for exactly one address in one tenant and mails the link. The token is
returned as well, because a client that sends its own mail still needs it. -/
def createInvitation {m : Type → Type} [Monad m] [Clock m] [RandomBytes m] {tenant : TenantId}
    (ports : Ports m) (config : TenantConfig tenant) (address : EmailAddress)
    (metadata : InvitationMetadata) (createdBy : Actor := .anonymous) :
    m (Option (Invitation tenant × CredentialValue)) := do
  let now ← Clock.now
  match ← randomValue 12, ← randomValue 16 with
  | .error _, _ => pure none
  | _, .error _ => pure none
  | .ok generated, .ok token =>
    let invitation : Invitation tenant :=
      { id := ⟨generated.encoded⟩
        address
        tokenDigest := ports.peppers.current.digest token
        metadata
        expiresAt := now.advance config.invitationLifetime
        createdBy }
    ports.store.createInvitation tenant invitation
    let _ ← ports.transport.send
      (invitationEmail config invitation (acceptLink config invitation.id token))
    pure (some (invitation, token))

/-- Rotating the token is what invalidates the old link, which is what AUTH-8.5 requires of a
resend: the person who was sent one twice can use either message and only the newer works. -/
def resendInvitation {m : Type → Type} [Monad m] [Clock m] [RandomBytes m] {tenant : TenantId}
    (ports : Ports m) (config : TenantConfig tenant) (id : InvitationId tenant) :
    m (Option CredentialValue) := do
  let now ← Clock.now
  match ← ports.store.invitationById tenant id with
  | none => pure none
  | some invitation =>
    if invitation.state != .pending then pure none
    else
      match ← randomValue 16 with
      | .error _ => pure none
      | .ok token =>
        let rotated :=
          { invitation with
            tokenDigest := ports.peppers.current.digest token
            expiresAt := now.advance config.invitationLifetime }
        if ← ports.store.commitInvitation tenant invitation rotated then
          let _ ← ports.transport.send
            (invitationEmail config rotated (acceptLink config id token))
          pure (some token)
        else pure none

def revokeInvitation {m : Type → Type} [Monad m] [Clock m] {tenant : TenantId} (ports : Ports m)
    (id : InvitationId tenant) : m Bool := do
  match ← ports.store.invitationById tenant id with
  | none => pure false
  | some invitation =>
    if invitation.state != .pending then pure false
    else ports.store.commitInvitation tenant invitation { invitation with state := .revoked }

/-- Expiry is not a stored state, so listing derives it rather than depending on a sweeper
having run (AUTH-8.9, AUTH-15.4.3). -/
inductive InvitationStanding where
  | pending
  | accepted
  | expired
  | revoked
  deriving DecidableEq, Repr, Inhabited

def standing {tenant : TenantId} (now : Timestamp) (invitation : Invitation tenant) :
    InvitationStanding :=
  match invitation.state with
  | .accepted => .accepted
  | .revoked => .revoked
  | .pending => if invitation.expiresAt ≤ now then .expired else .pending

def invitations {m : Type → Type} [Monad m] [Clock m] {tenant : TenantId} (ports : Ports m) :
    m (List (Invitation tenant × InvitationStanding)) := do
  let now ← Clock.now
  pure ((← ports.store.invitationsForTenant tenant).map fun i => (i, standing now i))

/--
Accepting. The token is checked here and the invitation is not spent yet; what it authorises is
an attempt for the invited address, which then runs the whole of §5 including the cross-device
code, so a link opened on a phone signs nobody in on that phone (AUTH-8.4).

The address comes from the invitation record. There is no parameter for one, which is what makes
AUTH-8.3 unbreakable here rather than merely unbroken.
-/
def acceptInvitation {m : Type → Type} [Monad m] [Clock m] [RandomBytes m] {tenant : TenantId}
    (ports : Ports m) (config : TenantConfig tenant) (id : InvitationId tenant)
    (token : CredentialValue) (requester : RequestContext) :
    m (Except AuthError (Outcome tenant)) := do
  let now ← Clock.now
  match ← ports.store.invitationById tenant id with
  | none => pure (.error .invitationNotPending)
  | some invitation =>
    match Invitation.verify now invitation (ports.peppers.present token) with
    | .error e => pure (.error e)
    | .ok grant =>
      match ← mintSecrets ports.peppers config with
      | .error _ => pure (.error .attemptNotLive)
      | .ok secrets =>
        match ← randomValue 12 with
        | .error _ => pure (.error .attemptNotLive)
        | .ok generated =>
          let attemptId : AttemptId tenant := ⟨generated.encoded⟩
          let (state, effects) :=
            Attempt.begin config now attemptId grant.address secrets requester (some id)
          let superseded ← ports.store.startAttempt tenant state
          for abandoned in superseded do
            ports.store.appendAudit tenant
              ⟨now, .anonymous, .attemptAbandoned abandoned .superseded⟩
          .ok <$> performAll ports config now effects

/-- Identity and tenant, and nothing else (AUTH-9.7). -/
def identify {m : Type → Type} [Monad m] [Clock m] {tenant : TenantId} (ports : Ports m)
    (credential : CredentialValue) : m (Option (SessionIdentity tenant)) := do
  let now ← Clock.now
  let digests := (ports.peppers.present credential).digests
  let rec search : List Digest → m (Option (Session tenant))
    | [] => pure none
    | digest :: rest => do
      match ← ports.store.sessionByDigest tenant now digest with
      | some session => pure (some session)
      | none => search rest
  pure ((← search digests).map fun session => ⟨session.account⟩)

end Authentication.Service
