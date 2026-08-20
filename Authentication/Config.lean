/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Authentication.Policy
public import Authentication.Template
public import Authentication.Tenant
import Authentication.Time

public section

namespace Authentication

structure Url where
  value : String
  deriving DecidableEq, Repr, Inhabited

/-- Held per tenant so that every emitted URL is built from it rather than from a global
constant. In this version every tenant resolves to the same origin, which is what makes a
per-tenant hostname later a configuration change rather than a rewrite (AUTH-4.3.4). -/
structure BaseUrl where
  origin : String
  deriving DecidableEq, Repr, Inhabited

namespace BaseUrl

/-- Tenants are distinguished by a path prefix on one shared origin, because OAuth providers
match redirect URIs exactly and a hostname per tenant would need a registration per tenant
(AUTH-4.3.2). -/
def tenantPath (tenant : TenantId) : String := "/t/" ++ tenant.value

def url (base : BaseUrl) (tenant : TenantId) (path : String) : Url :=
  ⟨base.origin ++ tenantPath tenant ++ path⟩

end BaseUrl

/-- Resolved per tenant from the first version, even though every tenant initially points at
the same operator domain: a row per tenant makes per-tenant sending domains a data change
rather than schema surgery (AUTH-10.2). -/
structure SendingIdentity where
  address : EmailAddress
  displayName : String
  replyTo : Option EmailAddress := none
  deriving DecidableEq, Repr, Inhabited

inductive SameSite where
  | lax
  | strict
  | none
  deriving DecidableEq, Repr, Inhabited

structure CookieSpec where
  name : String
  value : String
  path : String
  expiresAt : Timestamp
  secure : Bool
  httpOnly : Bool
  sameSite : SameSite
  deriving DecidableEq, Repr, Inhabited

namespace CookieSpec

/--
`Lax` is required rather than an oversight: the cookie has to survive a top-level navigation
arriving from a mail client, and `Strict` would make every same-device click look cross-device
(AUTH-5.2.4). The attributes are fixed here rather than passed in, so no caller can weaken
them.
-/
def forAttempt (tenant : TenantId) (value : String) (expiresAt : Timestamp) : CookieSpec :=
  { name := "auth_attempt"
    value
    path := BaseUrl.tenantPath tenant
    expiresAt
    secure := true
    httpOnly := true
    sameSite := .lax }

/-- The attributes AUTH-9.2 fixes, fixed here for the same reason `forAttempt` fixes its own: no
caller can weaken them because no caller supplies them. The path is supplied, because an
application mounted outside the tenant's path is never offered a cookie confined to it; what
choosing it costs is set out at `TenantConfig.sessionCookiePath`. -/
def forSession (path : String) (value : String) (expiresAt : Timestamp) : CookieSpec :=
  { name := "auth_session"
    value
    path
    expiresAt
    secure := true
    httpOnly := true
    sameSite := .lax }

end CookieSpec

/-!
## Post-sign-in redirect targets (AUTH-9.8)

An unvalidated `returnTo` is an open redirect, and an open redirect is worth more to a phisher
than the sign-in page it hangs off: the link really does come from the tenant's own domain.
-/

namespace ReturnTo

/-- What an allowlist entry is matched against: everything before a query or a fragment. What
follows is carried through, so an allowlisted page keeps the parameters it was asked for. -/
def base (target : String) : String :=
  String.ofList (target.toList.takeWhile fun c => c != '?' && c != '#')

/-- `//evil.example` is another origin wearing a path's clothing, and a backslash is one after a
browser has normalised it. -/
def isLocalPath (target : String) : Bool :=
  target.startsWith "/" && !target.startsWith "//" && !target.toList.contains '\\'

/--
An entry beginning with `/` is a path and matches only itself. Any other entry is an origin and
matches itself or anything below it, with the separator part of what is compared: without it an
allowlist naming `https://app.example.com` admits `https://app.example.com.evil.test`.
-/
def permits (allowlist : List String) (target : String) : Bool :=
  let candidate := base target
  if isLocalPath target then allowlist.contains candidate
  else allowlist.any fun entry =>
    !entry.startsWith "/" && (candidate == entry || candidate.startsWith (entry ++ "/"))

def resolve (allowlist : List String) (fallback : String) : Option String → String
  | some target => if permits allowlist target then target else fallback
  | none => fallback

end ReturnTo

/-- Configurable per tenant within a bounded range (AUTH-5.2.8). The bounds are carried as
proofs so an out-of-range lifetime cannot be constructed at all. -/
structure AttemptLifetime where
  duration : Duration
  atLeastFiveMinutes : Duration.minutes 5 ≤ duration
  atMostOneHour : duration ≤ Duration.hours 1

namespace AttemptLifetime

def standard : AttemptLifetime := ⟨Duration.minutes 15, by decide, by decide⟩

instance : Inhabited AttemptLifetime := ⟨standard⟩

def ofDuration? (d : Duration) : Option AttemptLifetime :=
  if h : Duration.minutes 5 ≤ d ∧ d ≤ Duration.hours 1 then some ⟨d, h.1, h.2⟩ else Option.none

end AttemptLifetime

/-- Everything that varies by organisation (AUTH-4.1.2). Indexed by the tenant it configures,
so a config and a state from different tenants cannot be passed to the same call. -/
structure TenantConfig (tenant : TenantId) where
  displayName : String
  baseUrl : BaseUrl
  sendingIdentity : SendingIdentity
  signupPolicy : SignupPolicy
  invitationOverridesAllowlist : Bool := true
  attemptLifetime : AttemptLifetime := .standard
  maxCodeEntries : Nat := 5
  emailedCodeEnabled : Bool := false
  stripPlusTags : Bool := false
  sessionIdleTimeout : Duration := Duration.days 14
  sessionAbsoluteLifetime : Duration := Duration.days 90
  invitationLifetime : Duration := Duration.days 7
  returnToAllowlist : List String := []
  /-- Where a sign-in lands when it asked for nowhere, or asked for somewhere it may not go. -/
  defaultReturnTo : String := "/"
  /-- How stale the last-seen time may become before validating a session writes it back. The
  idle timeout of AUTH-9.4 has to slide or it is merely a shorter absolute lifetime, but sliding
  it on every request makes a write out of every read; this is what that costs. -/
  sessionTouchInterval : Duration := Duration.minutes 5
  /-- The path the session cookie is issued with. The default confines it to the tenant's own
  routes, so one tenant's cookie is never offered to another's (AUTH-4.3.3). A browser offers a
  cookie only to paths at or below this one, so an application mounted anywhere else, which
  includes every application mounted at `/`, never receives it and can never call
  `Service.identify` for its own requests; such a client widens this, typically to `"/"`.

  Widening it does mean one tenant's session cookie is offered to another tenant's routes, and
  that is harmless rather than merely unlikely: a presented credential is resolved through
  `Store.sessionByDigest`, which is given the tenant it was presented to, and the store
  conformance suite requires a session to be invisible from every other tenant. The cookie
  arrives, resolves to nothing, and `identify` answers `none`, exactly as it would for a cookie
  that was never issued.

  What a client accepts by widening it is reach: the credential is then sent to everything
  served at or below the path named here, and keeping that to paths the client controls is the
  client's responsibility, not this library's. -/
  sessionCookiePath : String := BaseUrl.tenantPath tenant
  /-- Overridable per tenant, which is what AUTH-10.7 asks for: a client supplies its own
  renderer rather than filling in holes in one this library dictates. -/
  templates : EmailTemplates := .standard

/-- A target that is not allowed is not an error: it becomes the tenant's default, so a stale
bookmark lands somewhere rather than nowhere. -/
def TenantConfig.returnTo {tenant : TenantId} (config : TenantConfig tenant)
    (requested : Option String) : String :=
  ReturnTo.resolve config.returnToAllowlist config.defaultReturnTo requested

end Authentication
