/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Tests
import Tests.Sqlite

/-!
Most of the suite is theorems, which pass by compiling. What remains here are the checks that
have to be run: the conformance suite against a real backend, and the worked flows, whose
value is in the effects a theorem does not constrain.
-/

def main : IO UInt32 := do
  let checks := Tests.Flow.checks ++ (← Tests.Migrations.checks) ++ (← Tests.Sqlite.conformanceChecks)
    ++ (← Tests.EndToEnd.checks) ++ Tests.Sql.checks ++ Tests.Template.checks ++ (← Tests.Signup.checks)
    ++ (← Tests.Signup.invitationChecks) ++ (← Tests.Signup.existingAccountChecks)
    ++ (← Tests.Postmark.checks) ++ (← Tests.Postmark.flowChecks) ++ Tests.Ses.checks ++ (← Tests.RateLimit.checks)
    ++ (← Tests.RateLimit.serviceChecks) ++ (← Tests.RateLimit.floorChecks) ++ (← Tests.Session.checks) ++ (← Tests.Session.lifetimeChecks)
    ++ (← Tests.Session.accountChecks) ++ Tests.Session.returnToChecks
    ++ Tests.Suppression.parserChecks ++ (← Tests.Suppression.checks) ++ (← Tests.System.checks)
    ++ (← Tests.Http.checks) ++ (← Tests.Http.equalisationChecks) ++ (← Tests.Http.returnToChecks)
    ++ (← Tests.Http.humanCheckChecks) ++ (← Tests.Http.webhookChecks) ++ (← Tests.Webhooks.snsChecks)
    ++ (← Tests.Webhooks.postmarkChecks)
    ++ (← Tests.Ses.flowChecks) ++ (← Tests.Postgres.conformanceChecks)
  let failed := checks.filter fun (_, passed) => !passed
  for (name, _) in failed do
    IO.eprintln s!"FAILED: {name}"
  if failed.isEmpty then
    IO.println s!"{checks.length} checks passed"
    return 0
  else
    IO.eprintln s!"{failed.length} of {checks.length} checks failed"
    return 1
