/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Authentication.Attempt
import Authentication.Codec.Base32
import Authentication.Codec.Base64Url
import Authentication.Crypto.Hmac
import Authentication.Port.Clock
import Authentication.Port.Email
import Authentication.Response
import Authentication.Store

/-!
The interpreter at the edge (AUTH-3.1).

Every decision is taken by `Attempt.step`; this module only mints credentials, reads and writes
through the store, and performs the effects the state machine asked for. Nothing here decides
whether a sign-in may proceed.

Signup policy is not consulted yet: an address that completes an attempt gets an account.
Wiring AUTH-7 and invitations in is the next stage, and the place it goes is `issueSession`
below, where the account is created.
-/

namespace Authentication.Service

open Authentication.Codec

/-- The implementations chosen at startup (AUTH-3.5), together with the peppers in force. -/
structure Ports (m : Type → Type) where
  store : AuthStore m
  transport : EmailTransport m
  responsePolicy : SignInResponsePolicy m
  peppers : Crypto.PepperRing

/-- What the caller has to act on: the pages to show, the cookies to set, and the session
credential, if one was issued. The HTTP layer that turns these into a response arrives with the
integration target. -/
structure Outcome (tenant : TenantId) where
  views : List View := []
  setCookies : List CookieSpec := []
  clearCookies : List (String × String) := []
  session : Option CredentialValue := none
  sent : List SentMessageId := []
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
def revealedCode (peppers : Crypto.PepperRing) (token : CredentialValue) : CredentialValue :=
  ⟨Base32.encodeString ((peppers.current.derive "revealed-code" token).take 5)⟩

/-- The grouping is for the eye and the typing hand only. What is digested is the canonical
form, so a code typed back with or without the grouping is the same code. -/
def displayCode (code : CredentialValue) : String :=
  String.ofList (code.encoded.toList.take 4) ++ "-" ++ String.ofList (code.encoded.toList.drop 4)

/-- Accepts a code as it was transcribed, then digests the canonical form of it. This is what
makes the Crockford substitutions reachable: a person who typed `O` for `0`, dropped the
grouping hyphen, or used lower case has still typed the code. -/
def canonicalCode (typed : String) : Option CredentialValue :=
  (Base32.decodeString typed).map fun bytes => ⟨Base32.encodeString bytes⟩

private def emailedCodeOf (drawn : List UInt8) : CredentialValue :=
  let value := drawn.foldl (fun acc byte => acc * 256 + byte.toNat) 0 % 1000000
  let digits := toString value
  ⟨String.ofList (List.replicate (6 - digits.length) '0') ++ digits⟩

def mintSecrets {m : Type → Type} [Monad m] [RandomBytes m] {tenant : TenantId}
    (peppers : Crypto.PepperRing) (config : TenantConfig tenant) :
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
the requester typed (AUTH-5.2.11, AUTH-5.2.12). Templates the client can override per tenant
arrive with the transport. -/
private def signInEmail {tenant : TenantId} (config : TenantConfig tenant)
    (message : SignInEmail tenant) : OutboundEmail :=
  let requester :=
    match message.requester.ip, message.requester.approximateLocation with
    | some ip, some place => s!"from {ip}, near {place}"
    | some ip, none => s!"from {ip}"
    | none, some place => s!"from near {place}"
    | none, none => "from an unrecorded address"
  let code :=
    match message.emailedCode with
    | some value => s!"\n\nOr type this code instead: {value.encoded}"
    | none => ""
  { «from» := config.sendingIdentity
    to := message.recipient
    subject := s!"Sign in to {config.displayName}"
    textBody :=
      s!"Someone asked to sign in to {config.displayName} as {message.recipient.render}, " ++
      s!"{requester}, at {message.requestedAt.epochSeconds} (epoch seconds).\n\n" ++
      s!"To continue, open:\n{message.magicLink.value}{code}\n\n" ++
      "If this was not you, you can ignore this message. Nobody can sign in without opening " ++
      "the link above."
    replyTo := config.sendingIdentity.replyTo
    idempotencyKey := s!"attempt:{message.attempt.value}" }

private def issueSession {m : Type → Type} [Monad m] [RandomBytes m] {tenant : TenantId}
    (ports : Ports m) (config : TenantConfig tenant) (now : Timestamp)
    (subject : SessionSubject tenant) : m (Option CredentialValue) := do
  let identity := subject.address.normalise
  let existing ← ports.store.accountByIdentity tenant identity
  let account ←
    match existing with
    | some account => pure (some account.id)
    | none =>
      match ← randomValue 12 with
      | .error _ => pure none
      | .ok generated =>
        let account : Account tenant :=
          { id := ⟨generated.encoded⟩
            identity
            primaryEmail := subject.address
            createdAt := now }
        match ← ports.store.createAccount tenant account with
        | .ok created => pure (some created.account.id)
        | .error _ => pure ((← ports.store.accountByIdentity tenant identity).map (·.id))
  match account with
  | none => pure none
  | some accountId =>
    match ← randomValue 16 with
    | .error _ => pure none
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
      pure (some credential)

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
    let session ← issueSession ports config now subject
    pure { outcome with session }
  | .present view => pure { outcome with views := outcome.views ++ [view] }

private def performAll {m : Type → Type} [Monad m] [RandomBytes m] {tenant : TenantId}
    (ports : Ports m) (config : TenantConfig tenant) (now : Timestamp)
    (effects : List (Effect tenant)) : m (Outcome tenant) :=
  effects.foldlM (fun outcome effect => perform ports config now outcome effect) {}

/--
Begins a sign-in. The response comes from the policy rather than from what happened, and every
outcome takes the same path through this function, so what the client chose to say cannot be
undone by a difference in shape (AUTH-14.2).
-/
def begin {m : Type → Type} [Monad m] [Clock m] [RandomBytes m] {tenant : TenantId}
    (ports : Ports m) (config : TenantConfig tenant) (address : EmailAddress)
    (requester : RequestContext) : m (Outcome tenant × SignInResponse) := do
  let now ← Clock.now
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
    (event : AttemptEvent) : m (Except AuthError (Outcome tenant)) := do
  let now ← Clock.now
  match ← ports.store.attemptById tenant attempt with
  | none => pure (.error .attemptNotLive)
  | some state =>
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
  advance ports config attempt
    (.linkOpened (ports.peppers.present token) (cookie.map ports.peppers.present))

/-- The `POST` from the same-device landing page (AUTH-5.2.1). -/
def confirmSignIn {m : Type → Type} [Monad m] [Clock m] [RandomBytes m] {tenant : TenantId}
    (ports : Ports m) (config : TenantConfig tenant) (attempt : AttemptId tenant)
    (cookie : CredentialValue) : m (Except AuthError (Outcome tenant)) :=
  advance ports config attempt (.completionRequested (ports.peppers.present cookie))

/-- The code typed into the browser the flow began in. -/
def submitCode {m : Type → Type} [Monad m] [Clock m] [RandomBytes m] {tenant : TenantId}
    (ports : Ports m) (config : TenantConfig tenant) (attempt : AttemptId tenant)
    (typed : String) (cookie : CredentialValue) : m (Except AuthError (Outcome tenant)) :=
  match canonicalCode typed with
  | none => pure (.error .notOriginatingBrowser)
  | some code =>
    advance ports config attempt
      (.revealedCodeSubmitted (ports.peppers.present cookie) (ports.peppers.present code))

/-- The optional typed code from the mail body (AUTH-5.4). -/
def submitEmailedCode {m : Type → Type} [Monad m] [Clock m] [RandomBytes m] {tenant : TenantId}
    (ports : Ports m) (config : TenantConfig tenant) (attempt : AttemptId tenant)
    (typed : String) (cookie : CredentialValue) : m (Except AuthError (Outcome tenant)) :=
  advance ports config attempt
    (.emailedCodeSubmitted (ports.peppers.present cookie) (ports.peppers.present ⟨typed⟩))

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
