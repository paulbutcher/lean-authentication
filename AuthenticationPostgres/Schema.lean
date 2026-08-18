/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import AuthenticationSql

/-!
The Postgres backend's dialect and schema.

Objects are created in a dedicated `auth` schema so they cannot collide with the client's own,
while staying in the same database so that enlisting in the client's transaction remains
possible (AUTH-15.7.1). Timestamps are `bigint` epoch seconds, matching the `Clock` port
(AUTH-15.7.4).

There is no connection here, so that everything a client might want without one, the dialect and
the schema, is reachable without libpq. The driver adapter is in `AuthenticationPostgres.Store`.
-/

namespace Authentication.Postgres

open Authentication.Sql

/-- Postgres numbers parameters from one and spells the prefix `$`, and its objects live in the
`auth` schema rather than behind a name prefix. -/
def dialect : Dialect where
  placeholder n := s!"${n}"
  table name := "auth." ++ name

/--
The schema, embedded from the migration files this package ships in `migrations/postgres` so that
there is one copy of it rather than two that can drift.

Applying it is the client's: the library neither runs migrations nor records that they were run
(AUTH-15.7.1). This is here for a client that would rather apply the SQL through its own code than
its migration tool, and for the tests. On an empty database it is every migration in order, which
is all there is while there is only one.
-/
private def initialSql : String :=
  include_str "../migrations/postgres/20260818120000_authentication_initial.up.sql"

private def rateCountersSql : String :=
  include_str "../migrations/postgres/20260818130000_authentication_rate_counters.up.sql"

private def suppressionSql : String :=
  include_str "../migrations/postgres/20260818140000_authentication_suppression.up.sql"

def createSchemaSql : String := initialSql ++ rateCountersSql ++ suppressionSql

end Authentication.Postgres
