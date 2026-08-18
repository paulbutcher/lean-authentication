/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Authentication.Email
import Authentication.Tenant
import Authentication.Time

namespace Authentication

/-- Sends and code submissions are limited independently (AUTH-14.1.1), so one budget cannot be
spent to exhaust the other. -/
inductive LimitAction where
  | send
  | codeSubmission
  deriving DecidableEq, Repr, Inhabited

/--
What one use is counted against. All five are counted for every request and any one of them can
refuse it (AUTH-14.1.1).

`address` is deliberately not scoped to a tenant. Without it an attacker spraying one address
across many tenants multiplies the send budget by the number of tenants and mail-bombs a third
party through the library, which is the one failure here that harms someone who never used it.
-/
inductive LimitScope where
  | tenantAddress (tenant : TenantId) (address : NormalisedEmail)
  | address (address : NormalisedEmail)
  | sourceIp (ip : String)
  | tenant (tenant : TenantId)
  | global
  deriving DecidableEq, Repr, Inhabited

namespace LimitScope

/-- Length-prefixed, so the key is injective. A tenant id is the client's own string and may hold
anything, including whatever separator a simpler rendering would have chosen; two scopes sharing a
counter would spend one tenant's budget on another's traffic. -/
private def part (s : String) : String := s!"{s.length}:{s}"

private def addressText (a : NormalisedEmail) : String := a.localPart ++ "@" ++ a.domain.render

def key : LimitScope → String
  | .tenantAddress t a => "ta|" ++ part t.value ++ part (addressText a)
  | .address a => "a|" ++ part (addressText a)
  | .sourceIp ip => "ip|" ++ part ip
  | .tenant t => "t|" ++ part t.value
  | .global => "g|"

end LimitScope

namespace LimitAction

def key : LimitAction → String
  | .send => "send"
  | .codeSubmission => "code"

end LimitAction

/--
Chosen from configuration at startup, so a structure rather than a class (AUTH-3.5), and its own
port rather than part of `AuthStore` because atomic increment-and-test within a window is a
different access pattern at a different contention level from anything else stored here
(AUTH-15.6.1). Keeping it separate is also what lets a deployment leave `AuthStore` on its primary
database and put the counters elsewhere (AUTH-15.6.2).
-/
structure RateLimiter (m : Type → Type) where
  /--
  Counts one use of `action` against every scope and answers whether all of them stayed inside
  their limit. Counting and testing are one operation, so two concurrent callers cannot both be
  told they were the last one inside the budget.

  Every scope is counted even when another has already refused. The alternative lets a caller who
  is over one limit spend nothing against the others, which is the wrong way round: the request
  was still made.
  -/
  admit : LimitAction → Timestamp → List LimitScope → m Bool

namespace RateLimiter

/-- Admits everything. For tests, and for a client that has not chosen a limiter yet; it is not a
default, because AUTH-14.1.1 is a requirement and a library that quietly enforced nothing would be
claiming to meet it. -/
def unlimited (m : Type → Type) [Pure m] : RateLimiter m where
  admit _ _ _ := pure true

end RateLimiter

/-- Uses allowed within a window. -/
structure Limit where
  uses : Nat
  window : Duration
  deriving DecidableEq, Repr, Inhabited

/-- One budget per scope, for one action. -/
structure ActionLimits where
  tenantAddress : Limit
  address : Limit
  sourceIp : Limit
  tenant : Limit
  global : Limit
  deriving DecidableEq, Repr, Inhabited

namespace ActionLimits

def forScope (limits : ActionLimits) : LimitScope → Limit
  | .tenantAddress _ _ => limits.tenantAddress
  | .address _ => limits.address
  | .sourceIp _ => limits.sourceIp
  | .tenant _ => limits.tenant
  | .global => limits.global

end ActionLimits

/--
The numbers, which are the client's to set and not a tenant's: a tenant cannot be allowed to raise
its own budget, and the cross-tenant and global scopes do not belong to any one tenant at all.

The defaults are deliberately tight. AUTH-14.2.8 records that rate limiting does more work than
wording does in protecting against account enumeration, which only holds while a probe budget is
small enough to make an oracle worthless.
-/
structure RateLimits where
  send : ActionLimits :=
    { tenantAddress := ⟨3, Duration.hours 1⟩
      address := ⟨5, Duration.hours 1⟩
      sourceIp := ⟨20, Duration.hours 1⟩
      tenant := ⟨500, Duration.hours 1⟩
      global := ⟨5000, Duration.hours 1⟩ }
  /-- Guessing one attempt's code is already capped at five tries by AUTH-5.2.7; these budgets are
  what stops an attacker farming attempts to multiply that cap. -/
  codeSubmission : ActionLimits :=
    { tenantAddress := ⟨10, Duration.hours 1⟩
      address := ⟨20, Duration.hours 1⟩
      sourceIp := ⟨60, Duration.hours 1⟩
      tenant := ⟨2000, Duration.hours 1⟩
      global := ⟨20000, Duration.hours 1⟩ }
  deriving Inhabited

namespace RateLimits

def forAction (limits : RateLimits) : LimitAction → ActionLimits
  | .send => limits.send
  | .codeSubmission => limits.codeSubmission

end RateLimits

/-! ## The window -/

/-- Which fixed bucket an instant falls in. Buckets are the width of the window, so a use is only
ever recorded against the current one. -/
def bucketOf (limit : Limit) (now : Timestamp) : Int :=
  if limit.window.seconds == 0 then 0 else now.epochSeconds / (limit.window.seconds : Int)

/--
What a sliding window sees: everything counted in the current bucket, plus the part of the previous
bucket the window still covers.

Two counters rather than one because a single fixed window admits a double burst across its
boundary, which is exactly when an attacker who has read the documentation would send. They
approximate rather than reproduce a true sliding window; the approximation is even-handed, being
neither more nor less permissive as the position within the bucket moves.
-/
def slidingCount (limit : Limit) (now : Timestamp) (current previous : Nat) : Nat :=
  let window := limit.window.seconds
  if window == 0 then current + previous
  else
    let elapsed := (now.epochSeconds % (window : Int)).toNat
    current + previous * (window - elapsed) / window

/-- Whether a use just counted into `current` is inside the budget. -/
def within (limit : Limit) (now : Timestamp) (current previous : Nat) : Bool :=
  slidingCount limit now current previous ≤ limit.uses

end Authentication
