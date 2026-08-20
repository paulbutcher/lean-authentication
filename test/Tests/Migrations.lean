/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import AuthenticationSqlite

/-!
The migrations this package ships for a client to apply (AUTH-15.7.1).

The up files are already exercised everywhere, since `openInMemory` is built from them and the
whole suite runs against it. The down files are not exercised by anything else, and SQL that
nobody runs is SQL that does not work, so they are run here: applied, undone, and applied again.

Only the SQLite pair is run. The Postgres down drops the schema the conformance suite is using,
and interleaving that with the rest of the run would trade a real check for a fragile one.
-/

namespace Tests.Migrations
open Authentication

private def consentDown : String :=
  include_str "../../migrations/sqlite/20260820120000_authentication_consent.down.sql"

private def suppressionDown : String :=
  include_str "../../migrations/sqlite/20260818140000_authentication_suppression.down.sql"

private def rateCountersDown : String :=
  include_str "../../migrations/sqlite/20260818130000_authentication_rate_counters.down.sql"

private def initialDown : String :=
  include_str "../../migrations/sqlite/20260818120000_authentication_initial.down.sql"

/-- Newest first, which is the order a rollback undoes them in. Applying them the other way round
would leave whatever a later migration added. -/
private def down : String :=
  consentDown ++ suppressionDown ++ rateCountersDown ++ initialDown

private def authTables (db : SQLite) : IO Nat := do
  let stmt ← db.prepare "SELECT count(*) FROM sqlite_master WHERE type = 'table' AND name LIKE 'auth%'"
  let mut count := 0
  while ← stmt.step do
    count := (← stmt.columnInt64 0).toInt.toNat
  pure count

def checks : IO (List (String × Bool)) := do
  let db ← SQLite.openWith ":memory:" .readWriteCreate
  db.exec Sqlite.createSchemaSql
  let created ← authTables db
  db.exec down
  let dropped ← authTables db
  db.exec Sqlite.createSchemaSql
  let recreated ← authTables db
  pure
    [ ("migrations: the up file creates the tables", created > 0),
      ("migrations: the down file removes everything the up file created", dropped == 0),
      ("migrations: the up file applies again to the database the down file left",
        recreated == created) ]

end Tests.Migrations
