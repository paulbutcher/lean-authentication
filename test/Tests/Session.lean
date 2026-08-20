/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import AuthenticationSqlite

/-!
The session management surface (§9).

The two claims worth proving rather than sampling are here as theorems: that sliding the idle
timeout can never carry a session past its absolute lifetime, and that a redirect target which
is not allowlisted is never the one returned. Both are about pure total functions, and both are
the kind of mistake that would be invisible in the output that a check inspects.

The rest has to be driven: revocation that leaves a session answering, or a deactivated account
that a fresh magic link signs back in, look identical from inside the function that was supposed
to prevent them.
-/

namespace Tests.Session
open Authentication Authentication.Service

/-! ## The invariants -/

/-- The absolute lifetime is a ceiling, not a suggestion. Without this a session used every day
never ends, which is the failure AUTH-9.4 asks for two timeouts in order to avoid. -/
theorem refreshedIdleExpiry_within_absolute {tenant : TenantId} (s : Session tenant)
    (now : Timestamp) (idleTimeout : Duration) :
    (s.refreshedIdleExpiry now idleTimeout).epochSeconds ≤ s.absoluteExpiresAt.epochSeconds := by
  unfold Session.refreshedIdleExpiry
  by_cases h : s.absoluteExpiresAt ≤ now.advance idleTimeout
  · simp [h]
  · have h' : ¬ (s.absoluteExpiresAt.epochSeconds ≤ (now.advance idleTimeout).epochSeconds) := h
    simp only [h, if_false]
    omega

/-- An open redirect is a phishing amplifier precisely because the link comes from the tenant's
own domain, so what matters is not that allowed targets pass but that nothing else does
(AUTH-9.8). -/
theorem resolve_permitted (allowlist : List String) (fallback : String)
    (requested : Option String) :
    ReturnTo.resolve allowlist fallback requested = fallback
      ∨ ReturnTo.permits allowlist (ReturnTo.resolve allowlist fallback requested) := by
  cases requested with
  | none => exact Or.inl rfl
  | some target =>
    simp only [ReturnTo.resolve]
    by_cases h : ReturnTo.permits allowlist target
    · exact Or.inr (by simp [h])
    · exact Or.inl (by simp [h])

/-! ## The surface -/

initialize clockRef : IO.Ref Timestamp ← IO.mkRef ⟨1700000000⟩
initialize drawCounter : IO.Ref Nat ← IO.mkRef 0
initialize sentRef : IO.Ref (List OutboundEmail) ← IO.mkRef []

instance : Clock IO where
  now := clockRef.get

instance : RandomBytes IO where
  draw count := do
    let index ← drawCounter.modifyGet fun n => (n, n + 1)
    pure (.ok ((Crypto.Sha256.hashUtf8 s!"session-seed-{index}").extract 0 count))

def capturing : EmailTransport IO where
  send mail := do
    sentRef.modify (· ++ [mail])
    pure (.ok ⟨mail.idempotencyKey⟩)

private def address (raw : String) : EmailAddress := (EmailAddress.parse raw).toOption.getD default

def peppers : PepperRing :=
  { current := { keyId := ⟨"pepper-1"⟩, secret := Crypto.Sha256.hashUtf8 "test pepper" } }

def tenant : TenantId := ⟨"acme"⟩

private def portsOn (db : SQLite) : Ports IO :=
  { store := Sqlite.store db
    transport := capturing
    responsePolicy := SignInResponsePolicy.silent IO
    limiter := RateLimiter.unlimited IO
    responseFloor := ResponseFloor.immediate IO
    humanCheck := HumanCheck.unchecked IO
    peppers }

private def config : TenantConfig tenant :=
  { displayName := "Acme"
    baseUrl := ⟨"https://auth.example.com"⟩
    sendingIdentity :=
      { address := address "sign-in@auth.example.com", displayName := "Acme sign-in" }
    signupPolicy := .unrestricted
    returnToAllowlist := ["/dashboard", "https://app.example.com"] }

private def parameterFrom (body : String) (name : String) : Option String :=
  let rest := (body.splitOn (name ++ "=")).drop 1
  rest[0]?.map fun tail =>
    String.ofList (tail.toList.takeWhile fun c => c != '&' && c != '\n' && c != ' ')

private def cookieNamed {tenant : TenantId} (outcome : Outcome tenant) (name : String) :
    Option CookieSpec :=
  outcome.setCookies.find? (·.name == name)

private def nonceOf {tenant : TenantId} (outcome : Outcome tenant) : Option CredentialValue :=
  (cookieNamed outcome "auth_attempt").bind fun cookie =>
    match cookie.value.splitOn ":" with
    | [_, nonce] => some ⟨nonce⟩
    | _ => none

private def outcomeOf {t : TenantId} (result : Except AuthError (Outcome t)) : Outcome t :=
  match result with
  | .ok outcome => outcome
  | .error _ => {}

/-- One whole sign-in, driven the way a person drives it: read the link out of the mail, open it
on another device, type the code back into the browser that asked. -/
private def signIn (ports : Ports IO) (cfg : TenantConfig tenant) (raw : String)
    (requester : RequestContext := {}) : IO (Outcome tenant) := do
  sentRef.set []
  let (begun, _) ← begin ports cfg (address raw) requester
  let body := (((← sentRef.get)[0]?).map (·.textBody)).getD ""
  let attempt : AttemptId tenant := ⟨(parameterFrom body "attempt").getD ""⟩
  let token : CredentialValue := ⟨(parameterFrom body "token").getD ""⟩
  let _ ← openLink ports cfg attempt token none
  let typed := displayCode (revealedCode ports.peppers token)
  match nonceOf begun with
  | some nonce => outcomeOf <$> submitCode ports cfg attempt typed nonce requester
  | none => pure {}

private def accountOf (identity : Option (SessionIdentity tenant)) : AccountId tenant :=
  match identity with
  | some found => found.account
  | none => ⟨""⟩

def checks : IO (List (String × Bool)) := do
  clockRef.set ⟨1700000000⟩
  let db ← Sqlite.openInMemory
  let ports := portsOn db

  let laptop : RequestContext :=
    { ip := some "198.51.100.7", userAgent := some "Laptop/1.0",
      approximateLocation := some "Edinburgh" }
  let first ← signIn ports config "person@example.com" laptop
  let cookie := cookieNamed first "auth_session"
  let credential := first.session.getD ⟨""⟩
  let identity ← identify (tenant := tenant) ports config credential
  let account := accountOf identity

  -- A second sign-in from another browser, so there is something to revoke and something to
  -- leave alone.
  let second ← signIn ports config "person@example.com" { userAgent := some "Phone/2.0" }
  let otherCredential := second.session.getD ⟨""⟩
  let otherIdentity ← identify (tenant := tenant) ports config otherCredential
  let listed ← sessions (tenant := tenant) ports account credential
  let currentIds := (listed.filter (·.current)).map (·.id.value)
  let agents := listed.filterMap (·.userAgent)

  -- Revoking one, named with the account it is supposed to belong to.
  let target := (listed.find? fun s => !s.current).map (·.id)
  let strayAccount : AccountId tenant := ⟨"nobody"⟩
  let refusedRevoke ← match target with
    | some id => revokeSession (tenant := tenant) ports strayAccount id
    | none => pure true
  let revoked ← match target with
    | some id => revokeSession (tenant := tenant) ports account id
    | none => pure false
  let afterRevoke ← sessions (tenant := tenant) ports account credential
  let survivor ← identify (tenant := tenant) ports config credential
  let revokedIdentity ← identify (tenant := tenant) ports config otherCredential

  -- And then all of them.
  revokeAllSessions (tenant := tenant) ports account
  let afterAll ← sessions (tenant := tenant) ports account credential
  let noneSurvive ← identify (tenant := tenant) ports config credential

  pure
    [ ("session: a completed sign-in returns a session cookie (AUTH-9.2)",
        (cookie.map (·.value)) == some credential.encoded),
      ("session: the cookie is confined to the tenant's path (AUTH-4.3.3)",
        (cookie.map fun c => (c.path, c.secure, c.httpOnly, c.sameSite))
          == some (BaseUrl.tenantPath tenant, true, true, SameSite.lax)),
      ("session: the cookie's credential identifies the account (AUTH-9.7)", identity.isSome),
      ("session: each sign-in issues its own identifier (AUTH-9.3)",
        credential != otherCredential && listed.length == 2),
      ("session: both sessions belong to the one account",
        otherIdentity.map (·.account.value) == identity.map (·.account.value)),
      ("session: the listing says which session is asking (AUTH-9.5)",
        currentIds.length == 1),
      ("session: the listing carries what the browser said about itself (AUTH-9.5)",
        agents.length == 2 && agents.contains "Laptop/1.0" && agents.contains "Phone/2.0"),
      ("session: a session is not revocable through an account it does not belong to",
        !refusedRevoke),
      ("session: an account holder revokes one of their sessions (AUTH-9.5)",
        revoked && afterRevoke.length == 1 && revokedIdentity.isNone),
      ("session: revoking one leaves the others alone", survivor.isSome),
      ("session: revoking all of them leaves none (AUTH-9.6)",
        afterAll.isEmpty && noneSurvive.isNone) ]

private def otherTenant : TenantId := ⟨"beta"⟩

private def otherConfig : TenantConfig otherTenant :=
  { displayName := "Beta"
    baseUrl := ⟨"https://auth.example.com"⟩
    sendingIdentity :=
      { address := address "sign-in@auth.example.com", displayName := "Beta sign-in" }
    signupPolicy := .unrestricted }

/-- A tenant whose application is not mounted under the tenant path widens the cookie's path so
that the browser offers it at all, and the price is that another tenant's routes are offered it
too. The last check is what makes that price payable: a credential presented to a tenant it was
not issued for identifies nobody. -/
def cookiePathChecks : IO (List (String × Bool)) := do
  clockRef.set ⟨1700000000⟩
  let db ← Sqlite.openInMemory
  let ports := portsOn db
  let widened : TenantConfig tenant := { config with sessionCookiePath := "/" }
  let signedIn ← signIn ports widened "person@example.com"
  let cookie := cookieNamed signedIn "auth_session"
  let credential := signedIn.session.getD ⟨""⟩
  let own ← identify (tenant := tenant) ports widened credential
  let elsewhere ← identify (tenant := otherTenant) ports otherConfig credential

  pure
    [ ("session: the cookie is issued with the path the tenant configured",
        (cookie.map (·.path)) == some "/"),
      ("session: widening the path leaves the fixed attributes fixed (AUTH-9.2)",
        (cookie.map fun c => (c.secure, c.httpOnly, c.sameSite))
          == some (true, true, SameSite.lax)),
      ("session: a widened cookie identifies nobody at another tenant (AUTH-4.3.3)",
        own.isSome && elsewhere.isNone) ]

/-- The idle timeout has to slide to be an idle timeout, and has to stop sliding at the absolute
lifetime to be bounded. Both are worth driving through the store, because both are the kind of
thing an implementation can get right in the pure layer and drop on the way to a column. -/
def lifetimeChecks : IO (List (String × Bool)) := do
  let start : Timestamp := ⟨1700000000⟩
  let sliding : TenantConfig tenant :=
    { config with
      sessionIdleTimeout := Duration.days 1
      sessionAbsoluteLifetime := Duration.days 90
      sessionTouchInterval := Duration.minutes 5 }
  clockRef.set start
  let db ← Sqlite.openInMemory
  let ports := portsOn db
  let signedIn ← signIn ports config "person@example.com"
  let credential := signedIn.session.getD ⟨""⟩

  -- Used ten minutes in, which is what moves the idle expiry.
  clockRef.set (start.advance (Duration.minutes 10))
  let used ← identify (tenant := tenant) ports sliding credential
  -- A day and a minute after signing in: past the original idle expiry, inside the slid one.
  clockRef.set ((start.advance (Duration.days 1)).advance (Duration.minutes 1))
  let stillLive ← identify (tenant := tenant) ports sliding credential
  -- A further day with nothing happening, and it is gone.
  clockRef.set (start.advance (Duration.days 3))
  let idledOut ← identify (tenant := tenant) ports sliding credential

  -- An absolute lifetime shorter than the idle timeout, so every touch is capped by it.
  let capped : TenantConfig tenant :=
    { sliding with sessionAbsoluteLifetime := Duration.hours 1 }
  clockRef.set start
  let cappedDb ← Sqlite.openInMemory
  let cappedPorts := portsOn cappedDb
  let cappedIn ← signIn cappedPorts capped "person@example.com"
  let cappedCredential := cappedIn.session.getD ⟨""⟩
  clockRef.set (start.advance (Duration.minutes 30))
  let halfway ← identify (tenant := tenant) cappedPorts capped cappedCredential
  clockRef.set ((start.advance (Duration.hours 1)).advance (Duration.minutes 1))
  let expired ← identify (tenant := tenant) cappedPorts capped cappedCredential

  clockRef.set start
  pure
    [ ("session: using a session slides its idle timeout (AUTH-9.4)",
        used.isSome && stillLive.isSome),
      ("session: an unused session reaches its idle timeout", idledOut.isNone),
      ("session: use does not carry a session past its absolute lifetime (AUTH-9.4)",
        halfway.isSome && expired.isNone) ]

/-- The occasions AUTH-9.6 names, each of which has to revoke in the same call that changes the
account: the hazard is entirely in the gap between the two. -/
def accountChecks : IO (List (String × Bool)) := do
  clockRef.set ⟨1700000000⟩
  let db ← Sqlite.openInMemory
  let ports := portsOn db

  let signedIn ← signIn ports config "person@example.com"
  let credential := signedIn.session.getD ⟨""⟩
  let account := accountOf (← identify (tenant := tenant) ports config credential)

  let moved ← changePrimaryEmail (tenant := tenant) ports account (address "moved@example.com")
  let afterChange ← identify (tenant := tenant) ports config credential
  let underNewAddress ← ports.store.accountByIdentity tenant (address "moved@example.com").normalise

  -- Signing in again, then closing the account.
  let again ← signIn ports config "moved@example.com"
  let secondCredential := again.session.getD ⟨""⟩
  let closed ← deactivateAccount (tenant := tenant) ports account
  let afterClosing ← identify (tenant := tenant) ports config secondCredential
  -- A fresh magic link must not undo it, or revocation means nothing.
  let whileClosed ← signIn ports config "moved@example.com"
  let reopened ← reactivateAccount (tenant := tenant) ports account
  let afterReopening ← signIn ports config "moved@example.com"

  -- Taking an address another account already holds is refused, and changes nothing.
  let bystander ← signIn ports config "bystander@example.com"
  let bystanderAccount :=
    accountOf (← identify (tenant := tenant) ports config (bystander.session.getD ⟨""⟩))
  let collided ← changePrimaryEmail (tenant := tenant) ports bystanderAccount
    (address "moved@example.com")
  let bystanderSurvives ← identify (tenant := tenant) ports config (bystander.session.getD ⟨""⟩)

  let entries ← ports.store.auditEntries tenant
  let reasons := entries.filterMap fun entry =>
    match entry.event with
    | .accountSessionsRevoked _ reason => some reason
    | _ => none

  pure
    [ ("account: changing the primary address moves the account (AUTH-9.6)",
        moved matches .ok _ && (underNewAddress.map (·.id.value)) == some account.value),
      ("account: changing the primary address revokes every session (AUTH-9.6)",
        afterChange.isNone),
      ("account: deactivation revokes every session (AUTH-9.6)",
        closed matches .ok _ && afterClosing.isNone),
      ("account: a deactivated account cannot be signed back in",
        whileClosed.session.isNone
          && whileClosed.views == [.refused .accountDeactivated]),
      ("account: reactivating lets the account holder sign in again",
        reopened matches .ok _ && afterReopening.session.isSome),
      ("account: an address another account holds is refused (AUTH-15.4.2)",
        collided matches .error .duplicateAccount && bystanderSurvives.isSome),
      ("account: the log says why the sessions went (AUTH-13.7)",
        reasons.contains .primaryEmailChanged && reasons.contains .accountDeactivated) ]

/-- The targets an open redirect is built out of. The theorem says an unallowlisted target is
never returned; these say which targets are not allowlisted, which is the half a theorem about
`permits` would be assuming rather than establishing. -/
def returnToChecks : List (String × Bool) :=
  let resolve (requested : Option String) := config.returnTo requested
  [ ("returnTo: an allowlisted path is kept", resolve (some "/dashboard") == "/dashboard"),
    ("returnTo: its query survives", resolve (some "/dashboard?tab=1") == "/dashboard?tab=1"),
    ("returnTo: a path nobody allowed becomes the default (AUTH-9.8)",
      resolve (some "/admin") == "/"),
    ("returnTo: a protocol-relative target is another origin",
      resolve (some "//evil.example/x") == "/"),
    ("returnTo: a backslash is one after a browser has normalised it",
      resolve (some "/\\evil.example") == "/"),
    ("returnTo: an allowlisted origin is kept, with what is below it",
      resolve (some "https://app.example.com/welcome") == "https://app.example.com/welcome"),
    ("returnTo: a lookalike of an allowlisted origin is not it",
      resolve (some "https://app.example.com.evil.test/x") == "/"),
    ("returnTo: another origin entirely is not allowed",
      resolve (some "https://evil.test/") == "/"),
    ("returnTo: asking for nowhere lands at the default", resolve none == "/") ]

/-- Sweeping (AUTH-15.4.3). That the grace period is subtracted rather than added is the part
worth pinning: added, the sweep would remove records that are still live, and the first thing
anyone would notice is people being signed out.
-/
def purgeChecks : IO (List (String × Bool)) := do
  let start : Timestamp := ⟨1700000000⟩
  clockRef.set start
  let db ← Sqlite.openInMemory
  let ports := portsOn db
  let signedIn ← signIn ports config "person@example.com"
  let credential := signedIn.session.getD ⟨""⟩

  let immediately ← purgeExpired (tenant := tenant) ports
  let survived ← identify (tenant := tenant) ports config credential

  clockRef.set (start.advance (Duration.days 30))
  let swept ← purgeExpired (tenant := tenant) ports
  let again ← purgeExpired (tenant := tenant) ports

  clockRef.set start
  pure
    [ ("purge: a database with nothing expired loses nothing",
        immediately == {} && survived.isSome),
      ("purge: the session and the attempt behind it go once both are unreachable",
        swept.sessions == 1 && swept.attempts == 1),
      ("purge: and a second sweep finds nothing left to remove", again == {}) ]

end Tests.Session
