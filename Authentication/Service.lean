/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Authentication.Attempt
public import Authentication.Pepper
public import Authentication.Port.Clock
public import Authentication.Port.Email
public import Authentication.Port.HumanCheck
public import Authentication.Port.Latency
public import Authentication.Port.RateLimiter
public import Authentication.Store
public import Codec.Base64Url
import Authentication.Response
import Codec.Base32

/-!
The interpreter at the edge (AUTH-3.1).

Every decision about the sign-in flow is taken by `Attempt.step`; this module mints credentials,
reads and writes through the store, and performs the effects the state machine asked for.

The one decision taken here is signup policy, because AUTH-7.6 evaluates it at account creation
and account creation is here. Deciding it at `begin` would be worse than misplaced: it would
tell an unauthenticated caller whether an address may sign up, which is what AUTH-14.2 exists to
prevent. By the time `issueSession` runs, whoever is asking has proven control of the address.
-/

public section

namespace Authentication.Service

open Codec

/-- The implementations chosen at startup (AUTH-3.5), together with the peppers in force. -/
structure Ports (m : Type → Type) where
  store : AuthStore m
  transport : EmailTransport m
  responsePolicy : SignInResponsePolicy m
  limiter : RateLimiter m
  responseFloor : ResponseFloor m
  humanCheck : HumanCheck m
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
  refused : Option SignInRefusal := none
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
  refused : Option SignInRefusal := none

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
      -- account that already exists (AUTH-7.6). Deactivation is the exception, and has to be:
      -- revoking an account's sessions means nothing if the next magic link issues another.
      if account.status == .deactivated then pure (none, none, some .accountDeactivated)
      else pure (some account.id, none, none)
    | none =>
      match config.signupPolicy.evaluate subject.address grant.isSome
          config.invitationOverridesAllowlist with
      | .rejected reason => pure (none, none, some (.signup reason))
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
          | .signup .notInvited => .notInvited
          | .signup .domainNotAllowed => .domainNotAllowed
          | .accountDeactivated => .accountDeactivated)⟩
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
          absoluteExpiresAt := now.advance config.sessionAbsoluteLifetime
          userAgent := subject.requester.userAgent
          approximateLocation := subject.requester.approximateLocation }
      pure { session := some credential, admitted }

/--
Every message this library sends leaves through here, so an address the provider has already
refused is refused again without another attempt on it (AUTH-12.3). The transport is not asked,
because asking is exactly what spends the sending domain's reputation, and what it costs is
everyone else's mail rather than this one.
-/
private def deliver {m : Type → Type} [Monad m] (tenant : TenantId) (ports : Ports m)
    (mail : OutboundEmail) : m (Except SendError SentMessageId) := do
  match ← ports.store.deliveryRecord tenant mail.to.normalise with
  | some record =>
    if record.suppressed then pure (.error .addressSuppressed) else ports.transport.send mail
  | none => ports.transport.send mail

private def perform {m : Type → Type} [Monad m] [RandomBytes m] {tenant : TenantId}
    (ports : Ports m) (config : TenantConfig tenant) (now : Timestamp)
    (outcome : Outcome tenant) : Effect tenant → m (Outcome tenant)
  | .audit entry => do
    ports.store.appendAudit tenant entry
    pure outcome
  | .sendSignInEmail message => do
    match ← deliver tenant ports (signInEmail config message) with
    | .ok id => pure { outcome with sent := outcome.sent ++ [id] }
    | .error _ => pure outcome
  | .setAttemptCookie cookie => pure { outcome with setCookies := outcome.setCookies ++ [cookie] }
  | .clearAttemptCookie name path =>
    pure { outcome with clearCookies := outcome.clearCookies ++ [(name, path)] }
  | .issueSession subject => do
    let issued ← issueSession ports config now subject
    -- The cookie is built here rather than left to the client, so its attributes are the ones
    -- AUTH-9.2 fixes and not the ones a caller remembered. It expires with the absolute
    -- lifetime, since a cookie discarded at the idle timeout would end a session the store
    -- would still have honoured.
    let cookies := match issued.session with
      | none => outcome.setCookies
      | some credential =>
        outcome.setCookies ++
          [CookieSpec.forSession tenant credential.encoded
            (now.advance config.sessionAbsoluteLifetime)]
    pure
      { outcome with
        setCookies := cookies
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
      views := outcome.views.filter (· != .signedIn) ++ [.refused reason]
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
    (requester : RequestContext) (humanProof : Option String := none) :
    m (Outcome tenant × SignInResponse) :=
  -- Every outcome leaves through the same floor, including the ones that did no work at all.
  ports.responseFloor.normalise do
  let now ← Clock.now
  -- Ahead of the limiter, and deliberately: a request that fails the challenge spends none of
  -- the address's send budget. The other order would let anyone deny a person their own sign-in
  -- by failing challenges against their address all day (AUTH-14.1.8).
  if !(← ports.humanCheck.verify requester humanProof) then
    ports.store.appendAudit tenant ⟨now, .anonymous, .signInRejected .throttled⟩
    let response ← ports.responsePolicy.respond tenant .throttled
    return ({}, response)
  if !(← ports.limiter.admit .send now (limitScopes tenant address requester)) then
    -- The true outcome is recorded whatever the person was told (AUTH-14.2.6), and the policy
    -- chooses only what is said: it cannot decline to be limited (AUTH-14.2.5).
    ports.store.appendAudit tenant ⟨now, .anonymous, .signInRejected .throttled⟩
    let response ← ports.responsePolicy.respond tenant .throttled
    return ({}, response)
  -- Checked here as well as in `deliver`, so that a suppressed address costs an attempt record
  -- and a set of credentials rather than only a send that never happens. What the person is told
  -- is still the policy's to decide (AUTH-12.3).
  if ((← ports.store.deliveryRecord tenant address.normalise).map (·.suppressed)).getD false then
    ports.store.appendAudit tenant ⟨now, .anonymous, .signInRejected .addressSuppressed⟩
    let response ← ports.responsePolicy.respond tenant .addressSuppressed
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

/-- What an invitation operation produced. The delivery is reported rather than swallowed,
because a permanent failure is the client's to see: a suppressed address means the invitation
exists and nobody will ever receive it (AUTH-12.3). The token is here too, since a client that
sends its own mail still needs it. -/
structure InvitationIssued (tenant : TenantId) where
  invitation : Invitation tenant
  token : CredentialValue
  delivery : Except SendError SentMessageId

/-- Creates an invitation for exactly one address in one tenant and mails the link. -/
def createInvitation {m : Type → Type} [Monad m] [Clock m] [RandomBytes m] {tenant : TenantId}
    (ports : Ports m) (config : TenantConfig tenant) (address : EmailAddress)
    (metadata : InvitationMetadata) (createdBy : Actor := .anonymous) :
    m (Option (InvitationIssued tenant)) := do
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
    let delivery ← deliver tenant ports
      (invitationEmail config invitation (acceptLink config invitation.id token))
    pure (some { invitation, token, delivery })

/-- Rotating the token is what invalidates the old link, which is what AUTH-8.5 requires of a
resend: the person who was sent one twice can use either message and only the newer works. -/
def resendInvitation {m : Type → Type} [Monad m] [Clock m] [RandomBytes m] {tenant : TenantId}
    (ports : Ports m) (config : TenantConfig tenant) (id : InvitationId tenant) :
    m (Option (InvitationIssued tenant)) := do
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
          let delivery ← deliver tenant ports
            (invitationEmail config rotated (acceptLink config id token))
          pure (some { invitation := rotated, token, delivery })
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

/-! ## Bounces and suppression

The provider adapters turn a webhook into `DeliveryEvent`s; what happens to one is here, so that
both providers reach the same store through the same decision.
-/

/--
Records one delivery failure and returns what the address's history now says. A permanent
failure suppresses; a transient one is counted and nothing else, because a mailbox that was full
this morning is not an address nobody may write to again (AUTH-12.1).

Ingestion is not authenticated by this library. Verifying that the webhook came from the
provider belongs to the route that received it, which is the layer holding the signing secret,
and a client that skips it has handed anyone the ability to suppress any address (AUTH-13.2).
-/
def ingestDelivery {m : Type → Type} [Monad m] [Clock m] {tenant : TenantId} (ports : Ports m)
    (event : DeliveryEvent) : m (DeliveryRecord tenant) := do
  let now ← Clock.now
  let address := event.address.normalise
  let before ← ports.store.deliveryRecord tenant address
  let record ← ports.store.recordDeliveryFailure tenant address event.failure now event.detail
  -- Audited on the transition, not on every failure that arrives afterwards: the log answers
  -- when this address stopped receiving mail, and repeating it obscures that.
  match record.suppressedBy with
  | some reason =>
    if (before.bind (·.suppressedBy)).isNone then
      ports.store.appendAudit tenant ⟨now, .anonymous, .addressSuppressed address reason⟩
  | none => pure ()
  pure record

/-- Suppression the client asked for, from something it knows and this library does not. -/
def suppressAddress {m : Type → Type} [Monad m] [Clock m] {tenant : TenantId} (ports : Ports m)
    (address : EmailAddress) (detail : String := "") : m (DeliveryRecord tenant) := do
  let now ← Clock.now
  let normalised := address.normalise
  let record ← ports.store.suppressAddress tenant normalised now detail
  ports.store.appendAudit tenant ⟨now, .anonymous, .addressSuppressed normalised .client⟩
  pure record

/-- Whether mail to this address will be refused. -/
def suppressed {m : Type → Type} [Monad m] {tenant : TenantId} (ports : Ports m)
    (address : EmailAddress) : m Bool := do
  pure (((← ports.store.deliveryRecord tenant address.normalise).map (·.suppressed)).getD false)

/-- Addresses get fixed (AUTH-12.4). -/
def clearSuppression {m : Type → Type} [Monad m] [Clock m] {tenant : TenantId} (ports : Ports m)
    (address : EmailAddress) : m Unit := do
  let now ← Clock.now
  let normalised := address.normalise
  ports.store.clearSuppression tenant normalised
  ports.store.appendAudit tenant ⟨now, .anonymous, .suppressionCleared normalised⟩

/--
The addresses failing often enough to be worth telling the client about, worst first (AUTH-12.5).
Repeated bounces on an account's primary address are the single most common cause of "I cannot
log in", and it is a report rather than an alert because only the client knows whose address it
is.
-/
def deliveryReport {m : Type → Type} [Monad m] {tenant : TenantId} (ports : Ports m)
    (minimumFailures : Nat := 3) : m (List (DeliveryRecord tenant)) := do
  let records ← ports.store.deliveryRecords tenant
  let interesting := records.filter fun record =>
    record.suppressed || minimumFailures ≤ record.failures
  pure (interesting.mergeSort fun a b => decide (b.failures ≤ a.failures))

/-! ## Sessions

The surface an account holder's own session management is built on (§9). Like the invitation
operations above, none of these check a permission: the client decides who may revoke whose
session, and the library has no basis on which to (AUTH-13.2).
-/

private def sessionByCredential {m : Type → Type} [Monad m] {tenant : TenantId} (ports : Ports m)
    (now : Timestamp) (credential : CredentialValue) : m (Option (Session tenant)) :=
  let rec search : List Digest → m (Option (Session tenant))
    | [] => pure none
    | digest :: rest => do
      match ← ports.store.sessionByDigest tenant now digest with
      | some session => pure (some session)
      | none => search rest
  -- Every key still in its overlap window, so a rotation does not sign everyone out
  -- (AUTH-15.7.2).
  search (ports.peppers.present credential).digests

/--
Identity and tenant, and nothing else (AUTH-9.7).

Using a session slides its idle timeout, which is what makes the idle timeout of AUTH-9.4
different from a shorter absolute lifetime. The write happens only once the last-seen time has
gone stale by the tenant's touch interval, so an idle session is not kept alive by the writes
that record it being idle.
-/
def identify {m : Type → Type} [Monad m] [Clock m] {tenant : TenantId} (ports : Ports m)
    (config : TenantConfig tenant) (credential : CredentialValue) :
    m (Option (SessionIdentity tenant)) := do
  let now ← Clock.now
  match ← sessionByCredential ports now credential with
  | none => pure none
  | some session =>
    if session.dueForTouch now config.sessionTouchInterval then
      ports.store.touchSession tenant session.id now
        (session.refreshedIdleExpiry now config.sessionIdleTimeout)
    pure (some ⟨session.account⟩)

/-- The account's live sessions, newest first, with the one that asked marked (AUTH-9.5).
`presented` is the credential the request arrived with; without it no session is current. -/
def sessions {m : Type → Type} [Monad m] [Clock m] {tenant : TenantId} (ports : Ports m)
    (account : AccountId tenant) (presented : Option CredentialValue := none) :
    m (List (SessionSummary tenant)) := do
  let now ← Clock.now
  let current ← match presented with
    | none => pure none
    | some credential => pure ((← sessionByCredential ports now credential).map (·.id))
  let live ← ports.store.sessionsForAccount tenant now account
  pure ((live.mergeSort fun a b => decide (b.createdAt ≤ a.createdAt)).map fun session =>
    session.summary (current == some session.id))

/--
Revokes one session, and takes the account it is supposed to belong to rather than the session
alone. A client that routed a session id straight from a request parameter would otherwise be
handing whoever asked the ability to sign out anyone; this way the check is in the library and
the client cannot skip it by forgetting.

Reports whether there was such a live session to revoke.
-/
def revokeSession {m : Type → Type} [Monad m] [Clock m] {tenant : TenantId} (ports : Ports m)
    (account : AccountId tenant) (session : SessionId tenant) : m Bool := do
  let now ← Clock.now
  let live ← ports.store.sessionsForAccount tenant now account
  if live.any (·.id == session) then
    ports.store.revokeSession tenant now session
    ports.store.appendAudit tenant ⟨now, .anonymous, .sessionRevoked session⟩
    pure true
  else pure false

/-- Every session the account has, which is what AUTH-9.6 requires on the occasions
`RevocationReason` names, and what "sign out everywhere" is. -/
def revokeAllSessions {m : Type → Type} [Monad m] [Clock m] {tenant : TenantId} (ports : Ports m)
    (account : AccountId tenant) (reason : RevocationReason := .requested) : m Unit := do
  let now ← Clock.now
  ports.store.revokeSessionsForAccount tenant now account
  ports.store.appendAudit tenant ⟨now, .anonymous, .accountSessionsRevoked account reason⟩

/-! ## Account state

The operations AUTH-9.6 names. Each revokes in the same call as it changes, because the two
being separable is the whole hazard: an address that is no longer the account holder's, or an
account the client has closed, with a session still answering.
-/

/-- Changes the address the account is identified by and signs it out everywhere. Sessions go
because the previous address could have been the one under someone else's control (AUTH-9.6). -/
def changePrimaryEmail {m : Type → Type} [Monad m] [Clock m] {tenant : TenantId} (ports : Ports m)
    (account : AccountId tenant) (address : EmailAddress) : m (Except StoreError Unit) := do
  match ← ports.store.setPrimaryEmail tenant account address with
  | .error e => pure (.error e)
  | .ok () =>
    let now ← Clock.now
    ports.store.revokeSessionsForAccount tenant now account
    ports.store.appendAudit tenant ⟨now, .anonymous, .primaryEmailChanged account⟩
    ports.store.appendAudit tenant
      ⟨now, .anonymous, .accountSessionsRevoked account .primaryEmailChanged⟩
    pure (.ok ())

/-- Closes an account: its sessions go now, and `issueSession` refuses to make another, so a
magic link cannot undo this. -/
def deactivateAccount {m : Type → Type} [Monad m] [Clock m] {tenant : TenantId} (ports : Ports m)
    (account : AccountId tenant) : m (Except StoreError Unit) := do
  match ← ports.store.setAccountStatus tenant account .deactivated with
  | .error e => pure (.error e)
  | .ok () =>
    let now ← Clock.now
    ports.store.revokeSessionsForAccount tenant now account
    ports.store.appendAudit tenant ⟨now, .anonymous, .accountDeactivated account⟩
    ports.store.appendAudit tenant
      ⟨now, .anonymous, .accountSessionsRevoked account .accountDeactivated⟩
    pure (.ok ())

/-- Reopening grants nothing by itself: the account holder signs in again from the beginning. -/
def reactivateAccount {m : Type → Type} [Monad m] [Clock m] {tenant : TenantId} (ports : Ports m)
    (account : AccountId tenant) : m (Except StoreError Unit) := do
  match ← ports.store.setAccountStatus tenant account .active with
  | .error e => pure (.error e)
  | .ok () =>
    let now ← Clock.now
    ports.store.appendAudit tenant ⟨now, .anonymous, .accountReactivated account⟩
    pure (.ok ())

/-! ## Consent

Stored, never captured (AUTH-4.6.1). Nothing in this library asks anybody for consent, and the
sign-in flow in particular cannot: it shows the same page to an address it has never seen as to
one it knows, and a consent control that appeared on only the first of those would report which
was which before any mail was sent. The client asks somebody it has already signed in, whenever
it likes, and calls these.

Like the invitation and session operations, none of them check a permission (AUTH-13.2).
-/

/-- Records what somebody said about one subject. The version is the client's own, stored
verbatim and never read here (AUTH-4.6.2). -/
def recordConsent {m : Type → Type} [Monad m] [Clock m] {tenant : TenantId} (ports : Ports m)
    (account : AccountId tenant) (subject : ConsentSubject) (version : String) (act : ConsentAct)
    (actor : Actor := .anonymous) : m Unit := do
  let now ← Clock.now
  ports.store.recordConsent tenant { account, subject, version, act, recordedAt := now }
  ports.store.appendAudit tenant ⟨now, actor,
    match act with
    | .granted => .consentGranted account subject
    | .withdrawn => .consentWithdrawn account subject⟩

def grantConsent {m : Type → Type} [Monad m] [Clock m] {tenant : TenantId} (ports : Ports m)
    (account : AccountId tenant) (subject : ConsentSubject) (version : String)
    (actor : Actor := .anonymous) : m Unit :=
  recordConsent ports account subject version .granted actor

/-- Withdrawing is as easy as granting, and is the same call with the other answer. The entry
that granted stays where it is: what it says was agreed to in June is still true in December,
and a record that could be edited to say otherwise would be worth nothing as evidence. -/
def withdrawConsent {m : Type → Type} [Monad m] [Clock m] {tenant : TenantId} (ports : Ports m)
    (account : AccountId tenant) (subject : ConsentSubject) (version : String)
    (actor : Actor := .anonymous) : m Unit :=
  recordConsent ports account subject version .withdrawn actor

/-- Where the account stands on everything it has been asked about (AUTH-4.6.4). -/
def consents {m : Type → Type} [Monad m] {tenant : TenantId} (ports : Ports m)
    (account : AccountId tenant) : m (List ConsentState) :=
  Consent.state <$> ports.store.consentHistory tenant account

/-- Every entry, oldest first. `consents` answers what is true now; this is what was said, which
is the part that is evidence. -/
def consentHistory {m : Type → Type} [Monad m] {tenant : TenantId} (ports : Ports m)
    (account : AccountId tenant) : m (List (ConsentEntry tenant)) :=
  ports.store.consentHistory tenant account

/-- Who may be written to about this subject (AUTH-4.6.5). Deactivated accounts are among them:
somebody who closed their account did not thereby withdraw a consent, and the client decides
what its own closure means. -/
def consenting {m : Type → Type} [Monad m] {tenant : TenantId} (ports : Ports m)
    (subject : ConsentSubject) : m (List (AccountId tenant)) :=
  ports.store.consentingAccounts tenant subject

/-! ## Housekeeping -/

/--
Removes the attempts and sessions that expired more than `grace` ago (AUTH-15.4.3). The library
does not schedule this; a client runs it from whatever it already uses to run periodic work.

The grace period is what makes it safe to run against a database shared with processes whose
clocks differ slightly, and it is a parameter rather than a constant because how far apart those
clocks are is not something this library can know.

Sweeping is not audited. The audit log is the one thing this cannot remove, and a record of every
sweep would grow it in proportion to how often growth was being controlled.
-/
def purgeExpired {m : Type → Type} [Monad m] [Clock m] {tenant : TenantId} (ports : Ports m)
    (grace : Duration := Duration.days 1) : m PurgeCounts := do
  let now ← Clock.now
  ports.store.purgeExpired tenant ⟨now.epochSeconds - grace.seconds⟩

end Authentication.Service
