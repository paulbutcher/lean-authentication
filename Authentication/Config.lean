/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Authentication.Policy
import Authentication.Template
import Authentication.Tenant
import Authentication.Time

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

end CookieSpec

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
  /-- Overridable per tenant, which is what AUTH-10.7 asks for: a client supplies its own
  renderer rather than filling in holes in one this library dictates. -/
  templates : EmailTemplates := .standard

end Authentication
