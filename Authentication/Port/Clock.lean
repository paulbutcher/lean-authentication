/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Authentication.Time

namespace Authentication

/--
Time and randomness are ports rather than direct `IO` calls, so a test can pin the clock and
seed the source (AUTH-3.3). Both are resolved statically rather than chosen from configuration
at startup, so both may be classes (AUTH-3.5).
-/
class Clock (m : Type → Type) where
  now : m Timestamp

class RandomBytes (m : Type → Type) where
  /-- Fails rather than falling back to a weaker source: a credential drawn from a source that
  could not deliver is worse than a sign-in that did not happen (AUTH-5.3.1). -/
  draw : Nat → m (Except String ByteArray)

export Clock (now)

end Authentication
