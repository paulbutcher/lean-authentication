/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

namespace Authentication

/--
Normalising how long a sign-in takes (AUTH-14.2.4).

Sending mail takes measurably longer than not sending it, so a client that chose uniform silence
would find that choice undone by a timing oracle it never meant to open. Chosen from configuration
at startup, so a structure rather than a class (AUTH-3.5).

The floor belongs to the implementation and not to the call, which is deliberate: a duration the
caller passed could be made to vary with the outcome, and that is the leak this exists to close.
The library can ask for the floor and cannot choose it.
-/
structure ResponseFloor (m : Type → Type) where
  /-- Runs `action`, returning no earlier than the floor after it began. -/
  normalise : {α : Type} → m α → m α

namespace ResponseFloor

/--
Measures and pads. `IO.monoMsNow` rather than the `Clock` port because this is elapsed real time
and not the time a request is reasoning with, and because a test that pins the clock must not
thereby pin the floor to nothing.
-/
def sleeping (milliseconds : Nat) : ResponseFloor IO where
  normalise action := do
    let started ← IO.monoMsNow
    let result ← action
    let elapsed := (← IO.monoMsNow) - started
    if elapsed < milliseconds then
      IO.sleep (UInt32.ofNat (milliseconds - elapsed))
    pure result

/-- Serves no floor at all. For tests, and honest about what it is: a deployment wiring this in has
not met AUTH-14.2.4, whatever its response policy says. -/
def immediate (m : Type → Type) : ResponseFloor m where
  normalise action := action

end ResponseFloor

end Authentication
