/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import AuthenticationSqlite

/-!
Rate limiting (AUTH-14.1.1), against the reference limiter over a real SQLite database rather than
a fake, so the counting under test is the counting that runs.

AUTH-16.3 offers a property test for the limiter's monotonicity. It is a theorem here instead: the
claim is about a pure total function over two counters, and a limiter that grew more permissive as
the count rose would be a defect no example set would reliably catch.
-/

namespace Tests.RateLimit
open Authentication Authentication.Service

/-! ## The window -/

/--
The sliding window's count rises with the current bucket's count. This is the fact the limiter's
monotonicity rests on, isolated from the budget comparison so that the arithmetic of the two
buckets is settled once.

`slidingCount` adds the current bucket to the part of the previous one the window still covers.
`h` says `a` is at most `b`, and the conclusion says the counts they produce are ordered the same
way. `previous`, `now` and `limit` are held fixed across the two sides, so the comparison is
between two counts of the same window; the weighting applied to `previous` is therefore the
same on both, which is what makes the inequality hold whatever that weighting is.
-/
theorem slidingCount_monotone (limit : Limit) (now : Timestamp) {a b previous : Nat}
    (h : a ≤ b) : slidingCount limit now a previous ≤ slidingCount limit now b previous := by
  simp only [slidingCount]
  split <;> omega

/--
Counting more uses never turns a refusal into an admission. This is the property AUTH-16.3 asks
for, in the direction that matters: a limiter that grew more permissive as the count rose would
admit exactly the caller it exists to stop.

`within` answers `true` when the sliding count is inside the budget. `h` says `a` is at most
`b`, and `hb` says the larger count `b` was admitted; the conclusion is that the smaller count
`a` is admitted too. It is stated this way round because that is the form a proof about an
earlier request needs. The contrapositive is the sentence above: if `a` were refused, `b` would
be refused as well. `previous`, `now` and `limit` are shared between the two sides, so what
varies is the current count alone.
-/
theorem within_antitone (limit : Limit) (now : Timestamp) {a b previous : Nat} (h : a ≤ b)
    (hb : within limit now b previous = true) : within limit now a previous = true := by
  have := slidingCount_monotone limit now (previous := previous) h
  simp only [within, decide_eq_true_eq] at hb ⊢
  omega

/--
The previous bucket still counts, which is the whole reason for keeping two of them: a fixed
window would let a caller spend a full budget either side of a boundary. Without this the second
counter could be weighted away to nothing and the limiter would still look monotone.

`slidingCount` combines the current bucket's count with the part of the previous bucket the
window still covers. The conclusion is that the result is at least `current`, so the previous
bucket's contribution is never negative and never subtracts from what has just been counted.
`previous` is unconstrained, so this holds when the previous bucket is empty as well as when it
is full, and `now` is unconstrained, so it holds at every position within the bucket, including
the moment the window has just turned over.
-/
theorem previous_bucket_counts (limit : Limit) (now : Timestamp) (current previous : Nat) :
    current ≤ slidingCount limit now current previous := by
  simp only [slidingCount]
  split <;> exact Nat.le_add_right _ _

/-! ## Scope keys -/

private def address (raw : String) : EmailAddress := (EmailAddress.parse raw).toOption.getD default

private def normalised (raw : String) : NormalisedEmail := (address raw).normalise

/-! ## The limiter -/

initialize clockRef : IO.Ref Timestamp ← IO.mkRef ⟨1700000000⟩
initialize drawCounter : IO.Ref Nat ← IO.mkRef 0

instance : Clock IO where
  now := clockRef.get

instance : RandomBytes IO where
  draw count := do
    let index ← drawCounter.modifyGet fun n => (n, n + 1)
    pure (.ok ((Crypto.Sha256.hashUtf8 s!"ratelimit-seed-{index}").extract 0 count))

private def now : Timestamp := ⟨1700000000⟩

private def repeatedly (limiter : RateLimiter IO) (action : LimitAction)
    (scopes : List LimitScope) (times : Nat) : IO (List Bool) := do
  let mut answers := []
  for _ in [0 : times] do
    answers := answers ++ [← limiter.admit action now scopes]
  pure answers

def tenant : TenantId := ⟨"acme-rate"⟩

def tenantConfig : TenantConfig tenant :=
  { displayName := "Acme"
    baseUrl := ⟨"https://auth.example.com"⟩
    sendingIdentity :=
      { address := address "sign-in@auth.example.com", displayName := "Acme sign-in" }
    signupPolicy := .unrestricted }

def checks : IO (List (String × Bool)) := do
  let db ← Sqlite.openInMemory
  let limiter := Sql.rateLimiter Sqlite.dialect (Sqlite.connection db)
  let limits : RateLimits := {}

  let person := normalised "person@example.com"
  let sends ← repeatedly limiter .send [.tenantAddress tenant person] 5

  -- The same address in tenant after tenant, which is the attack the cross-tenant scope exists
  -- for: without it the send budget multiplies by the number of tenants and the mail lands on
  -- someone who never used this library (AUTH-16.7).
  let sprayed ← (List.range 7).mapM fun n =>
    limiter.admit .send now [.tenantAddress ⟨s!"tenant-{n}"⟩ person, .address person]

  -- Sends and code submissions are counted separately, so spending one cannot exhaust the other.
  let afterSends ← limiter.admit .codeSubmission now [.tenantAddress tenant person]

  let other := normalised "someone.else@example.com"
  let otherAddress ← limiter.admit .send now [.tenantAddress tenant other]

  pure
    [ ("rate limit: the budget admits its uses and then refuses",
        (sends.take limits.send.tenantAddress.uses).all id),
      ("rate limit: past the budget it refuses",
        (sends.drop limits.send.tenantAddress.uses).all (· == false)
          && sends.length > limits.send.tenantAddress.uses),
      ("rate limit: one address across many tenants hits the cross-tenant budget",
        (sprayed.take limits.send.address.uses).all id
          && (sprayed.drop limits.send.address.uses).all (· == false)),
      ("rate limit: code submissions have their own budget",
        afterSends == true),
      ("rate limit: another address is unaffected", otherAddress == true),
      -- The key is length-prefixed so that a tenant id holding the separator cannot be made to
      -- share a counter with another tenant, which would spend one tenant's budget on another's.
      ("rate limit: scope keys do not collide across a separator",
        LimitScope.key (.tenantAddress ⟨"a|b"⟩ person)
          != LimitScope.key (.tenantAddress ⟨"a"⟩ person)),
      ("rate limit: the scopes differ from each other",
        LimitScope.key (.address person) != LimitScope.key (.tenant tenant)) ]

/-! ## Through the service -/

/-- What `begin` does when refused: the same response as any other outcome, and an audit record of
what really happened (AUTH-14.2.4, AUTH-14.2.6). -/
def serviceChecks : IO (List (String × Bool)) := do
  let db ← Sqlite.openInMemory
  let sent ← IO.mkRef 0
  let ports : Ports IO :=
    { store := Sqlite.store db
      transport := { send := fun mail => do sent.modify (· + 1); pure (.ok ⟨mail.idempotencyKey⟩) }
      responsePolicy := SignInResponsePolicy.silent IO
      limiter := Sql.rateLimiter Sqlite.dialect (Sqlite.connection db)
      responseFloor := ResponseFloor.immediate IO
      humanCheck := HumanCheck.unchecked IO
      peppers := { current := { keyId := ⟨"pepper-1"⟩,
                                secret := Crypto.Sha256.hashUtf8 "test pepper" } } }
  let person := address "person@example.com"
  let requester : RequestContext := { ip := some "198.51.100.7" }
  let mut responses := []
  for _ in [0 : 5] do
    let (_, response) ← begin ports tenantConfig person requester
    responses := responses ++ [response]
  let sentCount ← sent.get
  let audit ← ports.store.auditEntries tenant
  let throttledEntries := audit.filter fun entry =>
    entry.event == .signInRejected .throttled
  pure
    [ ("rate limit: begin stops sending once the budget is spent",
        sentCount == ({} : RateLimits).send.tenantAddress.uses),
      ("rate limit: a refusal is told the same thing as a success",
        match responses with
        | [] => false
        | first :: rest => rest.all (· == first)),
      ("rate limit: the true outcome reaches the audit log whatever was said",
        throttledEntries.length == 5 - ({} : RateLimits).send.tenantAddress.uses) ]

/-! ## The response floor -/

private def recording (count : IO.Ref Nat) : ResponseFloor IO where
  normalise action := do
    count.modify (· + 1)
    action

/-- The floor is what stops a client's choice of wording being undone by a timing oracle
(AUTH-14.2.4), so what matters is that every outcome passes through it, the refusals that did no
work included. -/
def floorChecks : IO (List (String × Bool)) := do
  let db ← Sqlite.openInMemory
  let floored ← IO.mkRef 0
  let ports : Ports IO :=
    { store := Sqlite.store db
      transport := { send := fun mail => pure (.ok ⟨mail.idempotencyKey⟩) }
      responsePolicy := SignInResponsePolicy.silent IO
      limiter := Sql.rateLimiter Sqlite.dialect (Sqlite.connection db)
      responseFloor := recording floored
      humanCheck := HumanCheck.unchecked IO
      peppers := { current := { keyId := ⟨"pepper-1"⟩,
                                secret := Crypto.Sha256.hashUtf8 "test pepper" } } }
  let person := address "person.com"
  let attempts := 5
  for _ in [0 : attempts] do
    let _ ← begin ports tenantConfig person { ip := some "198.51.100.7" }
  let passes ← floored.get

  let started ← IO.monoMsNow
  let _ ← (ResponseFloor.sleeping 50).normalise (pure ())
  let elapsed := (← IO.monoMsNow) - started
  pure
    [ ("response floor: every sign-in leaves through it, refused ones included",
        passes == attempts),
      ("response floor: a request that finished early is held back to the floor",
        elapsed ≥ 50) ]

end Tests.RateLimit
