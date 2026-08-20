/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Authentication.Instances

/-!
The default `Clock` and `RandomBytes`.

The units are the point. Every lifetime in the library is epoch seconds, so a clock returning
milliseconds would put every expiry tens of thousands of years out and nothing else would
notice.
-/

namespace Tests.System
open Authentication

/-- 2020-01-01 and 2100-01-01. A clock in the wrong units lands outside them by orders of
magnitude. -/
private def plausible (t : Timestamp) : Bool :=
  1577836800 ≤ t.epochSeconds && t.epochSeconds ≤ 4102444800

def checks : IO (List (String × Bool)) := do
  let now ← Clock.now (m := IO)
  let drawn ← RandomBytes.draw (m := IO) 32
  let again ← RandomBytes.draw (m := IO) 32
  pure
    [ ("system clock: the time is epoch seconds, not another unit", plausible now),
      ("system randomness: a draw yields the number of bytes asked for",
        (drawn.toOption.map (·.size)) == some 32),
      ("system randomness: two draws differ",
        match drawn, again with
        | .ok a, .ok b => a != b
        | _, _ => false) ]

end Tests.System
