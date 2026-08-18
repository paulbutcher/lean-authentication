/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import AuthenticationSqlite

/-!
The whole cross-device flow, with no network and no database server (AUTH-16.5).

The fakes are the ones AUTH-16.6 asks for: a capturing transport, a settable clock, and a
seeded deterministic source of randomness. The store is not among them; it is SQLite in memory
running the statements production runs.

The token is read out of the captured mail rather than kept from the call that sent it, because
that is the only way it reaches a person, and a flow that works only when the caller remembers
the token is not the flow that ships.
-/

namespace Tests.EndToEnd
open Authentication Authentication.Service

initialize clockRef : IO.Ref Timestamp ← IO.mkRef ⟨1700000000⟩
initialize drawCounter : IO.Ref Nat ← IO.mkRef 0
initialize sentRef : IO.Ref (List OutboundEmail) ← IO.mkRef []

instance : Clock IO where
  now := clockRef.get

/-- Deterministic and distinct per draw, so a failure reproduces exactly. -/
instance : RandomBytes IO where
  draw count := do
    let index ← drawCounter.modifyGet fun n => (n, n + 1)
    pure (.ok ((Crypto.Sha256.hashUtf8 s!"conformance-seed-{index}").extract 0 count))

def capturingTransport : EmailTransport IO where
  send mail := do
    sentRef.modify (· ++ [mail])
    pure (.ok ⟨mail.idempotencyKey⟩)

def peppers : PepperRing :=
  { current := { keyId := ⟨"pepper-1"⟩, secret := Crypto.Sha256.hashUtf8 "test pepper" } }

def tenant : TenantId := ⟨"acme"⟩

def addressOf (raw : String) : EmailAddress := (EmailAddress.parse raw).toOption.getD default

def config : TenantConfig tenant :=
  { displayName := "Acme"
    baseUrl := ⟨"https://auth.example.com"⟩
    sendingIdentity :=
      { address := addressOf "sign-in@auth.example.com", displayName := "Acme sign-in" }
    signupPolicy := .unrestricted }

/-- Reads the value of a query parameter out of the mail body, the way opening the link does. -/
private def parameterFrom (body : String) (name : String) : Option String :=
  let marker := name ++ "="
  let rest := (body.splitOn marker).drop 1
  rest[0]?.map fun tail =>
    String.ofList (tail.toList.takeWhile fun c => c != '&' && c != '\n' && c != ' ')

private def cookieParts (value : String) : Option (String × String) :=
  match value.splitOn ":" with
  | [attempt, nonce] => some (attempt, nonce)
  | _ => none

private def viewsOf {t : TenantId} (result : Except AuthError (Outcome t)) : List View :=
  match result with
  | .ok outcome => outcome.views
  | .error _ => []

private def sessionOf {t : TenantId} (result : Except AuthError (Outcome t)) :
    Option CredentialValue :=
  match result with
  | .ok outcome => outcome.session
  | .error _ => none

private def errorOf {t : TenantId} (result : Except AuthError (Outcome t)) : Option AuthError :=
  match result with
  | .ok _ => none
  | .error e => some e

def checks : IO (List (String × Bool)) := do
  sentRef.set []
  let db ← Sqlite.openInMemory
  let ports : Ports IO :=
    { store := Sqlite.store db
      transport := capturingTransport
      responsePolicy := SignInResponsePolicy.silent IO
      limiter := RateLimiter.unlimited IO
      responseFloor := ResponseFloor.immediate IO
      peppers }
  let person := addressOf "person@example.com"

  -- Browser A asks for a link.
  let requester : RequestContext := { ip := some "198.51.100.7" }
  let (begun, response) ← begin ports config person requester
  let mail := (← sentRef.get)[0]?
  let body := (mail.map (·.textBody)).getD ""
  let attemptId := (parameterFrom body "attempt").getD ""
  let token := (parameterFrom body "token").getD ""
  let cookie := (begun.setCookies[0]?.bind fun c => cookieParts c.value)

  -- The link is opened on another device, which has no cookie.
  let opened ← openLink ports config ⟨attemptId⟩ ⟨token⟩ none
  -- That page shows the code, which it derives from the token it was opened with.
  let shownCode := displayCode (revealedCode peppers ⟨token⟩)

  -- A guess from a browser holding no attempt cookie.
  let guessed ← submitCode ports config ⟨attemptId⟩ shownCode ⟨"not-the-nonce"⟩ requester

  -- The code is typed back into browser A, in lower case and without the grouping hyphen.
  let typed := String.ofList ((shownCode.toList.filter (· != '-')).map Char.toLower)
  let completed ←
    match cookie with
    | some (_, nonce) => submitCode ports config ⟨attemptId⟩ typed ⟨nonce⟩ requester
    | none => pure (.error .notOriginatingBrowser)
  let session := sessionOf completed
  let identified ← match session with
    | some credential => identify (tenant := tenant) ports config credential
    | none => pure none

  -- The same attempt cannot be completed twice.
  let replayed ←
    match cookie with
    | some (_, nonce) => submitCode ports config ⟨attemptId⟩ typed ⟨nonce⟩ requester
    | none => pure (.error .notOriginatingBrowser)

  let audit ← ports.store.auditEntries tenant

  -- A second flow, this time finished on the device the link was opened on.
  let (secondBegun, _) ← begin ports config person {}
  let secondBody := ((← sentRef.get)[1]?.map (·.textBody)).getD ""
  let secondAttempt := (parameterFrom secondBody "attempt").getD ""
  let secondToken := (parameterFrom secondBody "token").getD ""
  let secondCookie := (secondBegun.setCookies[0]?.bind fun c => cookieParts c.value)
  let sameDevice ←
    match secondCookie with
    | some (_, nonce) => openLink ports config ⟨secondAttempt⟩ ⟨secondToken⟩ (some ⟨nonce⟩)
    | none => pure (.error .notOriginatingBrowser)
  let confirmed ←
    match secondCookie with
    | some (_, nonce) => confirmSignIn ports config ⟨secondAttempt⟩ ⟨nonce⟩
    | none => pure (.error .notOriginatingBrowser)

  -- The first flow's session survives the second sign-in, and both belong to one account.
  let stillValid ← match session with
    | some credential => identify (tenant := tenant) ports config credential
    | none => pure none

  pure
    [ ("flow: a link is sent when a sign-in begins", (← sentRef.get).length == 2),
      ("flow: the mail names the tenant in its subject",
        (mail.map (·.subject)) == some "Sign in to Acme"),
      ("flow: the mail states where the request came from",
        (mail.map fun m => m.textBody.splitOn "198.51.100.7" |>.length) == some 2),
      ("flow: the mail carries an idempotency key derived from the attempt",
        (mail.map (·.idempotencyKey)) == some s!"attempt:{attemptId}"),
      ("flow: the response is the silent default whatever happened",
        response == uniformSilence tenant .linkSent),
      ("flow: beginning a sign-in sets an attempt cookie", begun.setCookies.length == 1),
      ("flow: the attempt cookie is scoped to the tenant path",
        (begun.setCookies[0]?.map (·.path)) == some "/t/acme"),
      ("flow: the attempt cookie is Secure, HttpOnly and SameSite=Lax",
        (begun.setCookies[0]?.map fun c => (c.secure, c.httpOnly, c.sameSite))
          == some (true, true, SameSite.lax)),
      ("flow: opening the link cross-device shows the code",
        viewsOf opened == [.showVerificationCode]),
      ("flow: opening the link cross-device issues no session", (sessionOf opened).isNone),
      ("flow: a code from a browser without the attempt cookie is refused",
        errorOf guessed == some .notOriginatingBrowser),
      ("flow: the code typed into the originating browser completes the attempt",
        viewsOf completed == [.signedIn]),
      ("flow: completing the attempt issues a session", session.isSome),
      ("flow: the session identifies an account in this tenant", identified.isSome),
      ("flow: the same code cannot be used twice",
        errorOf replayed == some .attemptNotLive),
      ("flow: the attempt is audited from creation to session",
        audit.length == 4),
      ("flow: opening the link same-device offers the button",
        viewsOf sameDevice == [.confirmSignIn]),
      ("flow: the button completes the attempt on that device",
        viewsOf confirmed == [.signedIn]),
      ("flow: the second sign-in issues a different session",
        (sessionOf confirmed).isSome && (sessionOf confirmed) != session),
      ("flow: the first session is still valid after the second sign-in", stillValid.isSome),
      ("flow: both sessions belong to the same account",
        (← match sessionOf confirmed with
          | some credential => identify (tenant := tenant) ports config credential
          | none => pure none).map (·.account.value)
          == identified.map (·.account.value)) ]

end Tests.EndToEnd
