/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public section

-- Exposed because the bounds `AttemptLifetime` carries as proofs (`Config.lean`) are discharged
-- by `decide`, which has to reduce these definitions rather than reason about them.
@[expose] section

namespace Authentication

/-- Epoch seconds, matching what backends store (AUTH-15.7.4). -/
structure Timestamp where
  epochSeconds : Int
  deriving DecidableEq, Repr, Inhabited

structure Duration where
  seconds : Nat
  deriving DecidableEq, Repr, Inhabited

namespace Duration

def minutes (n : Nat) : Duration := ⟨n * 60⟩
def hours (n : Nat) : Duration := ⟨n * 3600⟩
def days (n : Nat) : Duration := ⟨n * 86400⟩

instance : LE Duration := ⟨fun a b => a.seconds ≤ b.seconds⟩

instance (a b : Duration) : Decidable (a ≤ b) :=
  inferInstanceAs (Decidable (a.seconds ≤ b.seconds))

end Duration

namespace Timestamp

def advance (t : Timestamp) (d : Duration) : Timestamp := ⟨t.epochSeconds + d.seconds⟩

instance : LE Timestamp := ⟨fun a b => a.epochSeconds ≤ b.epochSeconds⟩
instance : LT Timestamp := ⟨fun a b => a.epochSeconds < b.epochSeconds⟩

instance (a b : Timestamp) : Decidable (a ≤ b) :=
  inferInstanceAs (Decidable (a.epochSeconds ≤ b.epochSeconds))

instance (a b : Timestamp) : Decidable (a < b) :=
  inferInstanceAs (Decidable (a.epochSeconds < b.epochSeconds))

end Timestamp

end Authentication
