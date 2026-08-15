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

There is no connection here. `Authentication.Sql.sqlAuthStore` needs a driver that can bind
parameters and report rows affected, and no such driver exists for this toolchain; see
`KNOWN_ISSUES.md`. What this module supplies is everything that does not need one, so that
adding a driver is an adapter and not a backend.
-/

namespace Authentication.Postgres

open Authentication.Sql

/-- Postgres numbers parameters from one and spells the prefix `$`, and its objects live in the
`auth` schema rather than behind a name prefix. -/
def dialect : Dialect where
  placeholder n := s!"${n}"
  table name := "auth." ++ name

/--
The schema. Idempotent, so a client running it at startup gets the same result as one that runs
it through a migration tool.

It creates; it does not migrate. A database created by an earlier version keeps that version's
columns, because `IF NOT EXISTS` does nothing to a table that already exists. That is survivable
only while the schema has no deployments to preserve; see `KNOWN_ISSUES.md`.
-/
def createSchemaSql : String := "
  CREATE SCHEMA IF NOT EXISTS auth;
  CREATE TABLE IF NOT EXISTS auth.accounts (
    tenant text NOT NULL,
    id text NOT NULL,
    identity_local text NOT NULL,
    identity_domain text NOT NULL,
    sending_local text NOT NULL,
    sending_domain text NOT NULL,
    status text NOT NULL,
    created_at bigint NOT NULL,
    PRIMARY KEY (tenant, id),
    UNIQUE (tenant, identity_local, identity_domain)
  );
  CREATE TABLE IF NOT EXISTS auth.account_emails (
    tenant text NOT NULL,
    account_id text NOT NULL,
    local text NOT NULL,
    domain text NOT NULL,
    PRIMARY KEY (tenant, account_id, local, domain)
  );
  CREATE TABLE IF NOT EXISTS auth.attempts (
    tenant text NOT NULL,
    id text NOT NULL,
    address_local text NOT NULL,
    address_domain text NOT NULL,
    identity_local text NOT NULL,
    identity_domain text NOT NULL,
    phase text NOT NULL,
    magic_key text NOT NULL,
    magic_bytes text NOT NULL,
    code_key text NOT NULL,
    code_bytes text NOT NULL,
    emailed_key text,
    emailed_bytes text,
    nonce_key text NOT NULL,
    nonce_bytes text NOT NULL,
    failed_entries bigint NOT NULL,
    expires_at bigint NOT NULL,
    requester_ip text,
    requester_agent text,
    requester_location text,
    invitation_id text,
    PRIMARY KEY (tenant, id)
  );
  CREATE UNIQUE INDEX IF NOT EXISTS attempts_live
    ON auth.attempts (tenant, identity_local, identity_domain)
    WHERE phase IN ('pending', 'revealed');
  CREATE TABLE IF NOT EXISTS auth.sessions (
    tenant text NOT NULL,
    id text NOT NULL,
    account_id text NOT NULL,
    digest_key text NOT NULL,
    digest_bytes text NOT NULL,
    created_at bigint NOT NULL,
    last_seen_at bigint NOT NULL,
    idle_expires_at bigint NOT NULL,
    absolute_expires_at bigint NOT NULL,
    user_agent text,
    location text,
    revoked_at bigint,
    PRIMARY KEY (tenant, id)
  );
  CREATE INDEX IF NOT EXISTS sessions_digest
    ON auth.sessions (tenant, digest_key, digest_bytes);
  CREATE TABLE IF NOT EXISTS auth.invitations (
    tenant text NOT NULL,
    id text NOT NULL,
    address_local text NOT NULL,
    address_domain text NOT NULL,
    token_key text NOT NULL,
    token_bytes text NOT NULL,
    metadata text NOT NULL,
    state text NOT NULL,
    expires_at bigint NOT NULL,
    created_by text,
    consumed_at bigint,
    PRIMARY KEY (tenant, id)
  );
  CREATE TABLE IF NOT EXISTS auth.audit (
    seq bigint GENERATED ALWAYS AS IDENTITY PRIMARY KEY,
    tenant text NOT NULL,
    occurred_at bigint NOT NULL,
    actor_ref text,
    kind text NOT NULL,
    subject text NOT NULL,
    detail text NOT NULL
  );
  CREATE INDEX IF NOT EXISTS audit_tenant ON auth.audit (tenant, seq);
"

end Authentication.Postgres
