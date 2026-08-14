/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Tests

/-!
Most of the suite is theorems, which pass by compiling. What remains here are the checks that
have to be run: the worked flow of `Tests.Flow`, whose value is in the effects a theorem does
not constrain.
-/

def main : IO UInt32 := do
  let failed := Tests.Flow.checks.filter fun (_, passed) => !passed
  for (name, _) in failed do
    IO.eprintln s!"FAILED: {name}"
  if failed.isEmpty then
    IO.println s!"{Tests.Flow.checks.length} checks passed"
    return 0
  else
    IO.eprintln s!"{failed.length} of {Tests.Flow.checks.length} checks failed"
    return 1
