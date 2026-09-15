/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import AuthSeal
import Authentication.Instances

def main (args : List String) : IO UInt32 := do
  let outcome ← match AuthSeal.parseCommand args with
    | .error message => pure (.error message)
    | .ok command => AuthSeal.run command
  match outcome with
  | .error message => IO.eprintln message; pure 1
  | .ok output => IO.println output; pure 0
