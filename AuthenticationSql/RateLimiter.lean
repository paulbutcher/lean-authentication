/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Authentication
import AuthenticationSql.Connection

/-!
The reference `RateLimiter`, over the same SQL backends as `AuthStore` (AUTH-15.6.3).

Sharing the backend is allowed and is not free: these counters are the hottest write path in the
library, and on a single-writer backend they contend with everything else (AUTH-15.8.3). The port
is separate precisely so that a deployment which feels that can point the limiter elsewhere without
moving its accounts (AUTH-15.6.2).
-/

namespace Authentication.Sql

private def counters : TableName := ⟨"rate_counters"⟩

/--
Counts one use and returns the new total for the bucket.

The update is the common path and is one statement, so two callers cannot both read the same total
and both write back one more than it. The insert runs only when a bucket is new, and losing the
race to insert is expected rather than exceptional: whoever lost re-runs the update, which by then
finds the row the winner created.
-/
private def bump {m : Type → Type} [Monad m] (c : SqlConnection m) (d : Dialect)
    (scope action : String)
    (bucket : Int) : m Nat := do
  let increment :=
    sql!"UPDATE {counters} SET uses = uses + 1
         WHERE scope_key = {scope} AND action = {action} AND bucket = {bucket}
         RETURNING uses"
  match ← c.first d increment with
  | some row => pure (row.nat 0)
  | none =>
    let inserted ← c.affected d
      sql!"INSERT INTO {counters} (scope_key, action, bucket, uses)
           VALUES ({scope}, {action}, {bucket}, 1)
           ON CONFLICT DO NOTHING"
    if inserted == 1 then
      -- A new bucket means every bucket before the previous one is now unreachable by any window.
      -- Sweeping here rather than on a timer keeps growth bounded without a second moving part,
      -- and costs one statement per key per window rather than one per request.
      let _ ← c.affected d
        sql!"DELETE FROM {counters}
             WHERE scope_key = {scope} AND action = {action} AND bucket < {bucket - 1}"
      pure 1
    else
      match ← c.first d increment with
      | some row => pure (row.nat 0)
      | none => pure 1

private def previousUses {m : Type → Type} [Monad m] (c : SqlConnection m) (d : Dialect)
    (scope action : String)
    (bucket : Int) : m Nat := do
  let row ← c.first d
    sql!"SELECT uses FROM {counters}
         WHERE scope_key = {scope} AND action = {action} AND bucket = {bucket - 1}"
  pure (match row with | some row => row.nat 0 | none => 0)

/--
Every scope is counted before any answer is given, so a request refused by one scope still spends
its budget in the others: the request was made, whatever it was told.
-/
def rateLimiter {m : Type → Type} [Monad m] (d : Dialect) (c : SqlConnection m)
    (limits : RateLimits := {}) : RateLimiter m where
  admit action now scopes := do
    let actionLimits := limits.forAction action
    let mut admitted := true
    for scope in scopes do
      let limit := actionLimits.forScope scope
      let bucket := bucketOf limit now
      let current ← bump c d scope.key action.key bucket
      let previous ← previousUses c d scope.key action.key bucket
      if !within limit now current previous then
        admitted := false
    pure admitted

end Authentication.Sql
