/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import AuthenticationSqlite

/-!
The shipped conformance suite, run against the SQLite backend in memory (AUTH-15.5.2,
AUTH-16.5). There is no hand-written fake: these checks run the statements production runs,
which is what makes them evidence about the shipped code.
-/

namespace Tests.Sqlite
open Authentication

def conformanceChecks : IO (List (String × Bool)) := do
  let db ← Sqlite.openInMemory
  let results ← Store.Conformance.run (Sqlite.store db)
  pure (results.map fun check => (s!"store: {check.name}", check.passed))

end Tests.Sqlite
