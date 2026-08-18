CREATE TABLE IF NOT EXISTS auth_accounts (
  tenant TEXT NOT NULL,
  id TEXT NOT NULL,
  identity_local TEXT NOT NULL,
  identity_domain TEXT NOT NULL,
  sending_local TEXT NOT NULL,
  sending_domain TEXT NOT NULL,
  status TEXT NOT NULL,
  created_at INTEGER NOT NULL,
  PRIMARY KEY (tenant, id),
  UNIQUE (tenant, identity_local, identity_domain)
);
CREATE TABLE IF NOT EXISTS auth_account_emails (
  tenant TEXT NOT NULL,
  account_id TEXT NOT NULL,
  local TEXT NOT NULL,
  domain TEXT NOT NULL,
  PRIMARY KEY (tenant, account_id, local, domain)
);
CREATE TABLE IF NOT EXISTS auth_attempts (
  tenant TEXT NOT NULL,
  id TEXT NOT NULL,
  address_local TEXT NOT NULL,
  address_domain TEXT NOT NULL,
  identity_local TEXT NOT NULL,
  identity_domain TEXT NOT NULL,
  phase TEXT NOT NULL,
  magic_key TEXT NOT NULL,
  magic_bytes TEXT NOT NULL,
  code_key TEXT NOT NULL,
  code_bytes TEXT NOT NULL,
  emailed_key TEXT,
  emailed_bytes TEXT,
  nonce_key TEXT NOT NULL,
  nonce_bytes TEXT NOT NULL,
  failed_entries INTEGER NOT NULL,
  expires_at INTEGER NOT NULL,
  requester_ip TEXT,
  requester_agent TEXT,
  requester_location TEXT,
  invitation_id TEXT,
  PRIMARY KEY (tenant, id)
);
CREATE UNIQUE INDEX IF NOT EXISTS auth_attempts_live
  ON auth_attempts (tenant, identity_local, identity_domain)
  WHERE phase IN ('pending', 'revealed');
CREATE TABLE IF NOT EXISTS auth_sessions (
  tenant TEXT NOT NULL,
  id TEXT NOT NULL,
  account_id TEXT NOT NULL,
  digest_key TEXT NOT NULL,
  digest_bytes TEXT NOT NULL,
  created_at INTEGER NOT NULL,
  last_seen_at INTEGER NOT NULL,
  idle_expires_at INTEGER NOT NULL,
  absolute_expires_at INTEGER NOT NULL,
  user_agent TEXT,
  location TEXT,
  revoked_at INTEGER,
  PRIMARY KEY (tenant, id)
);
CREATE INDEX IF NOT EXISTS auth_sessions_digest
  ON auth_sessions (tenant, digest_key, digest_bytes);
CREATE TABLE IF NOT EXISTS auth_invitations (
  tenant TEXT NOT NULL,
  id TEXT NOT NULL,
  address_local TEXT NOT NULL,
  address_domain TEXT NOT NULL,
  token_key TEXT NOT NULL,
  token_bytes TEXT NOT NULL,
  metadata TEXT NOT NULL,
  state TEXT NOT NULL,
  expires_at INTEGER NOT NULL,
  created_by TEXT,
  consumed_at INTEGER,
  PRIMARY KEY (tenant, id)
);
CREATE TABLE IF NOT EXISTS auth_audit (
  seq INTEGER PRIMARY KEY AUTOINCREMENT,
  tenant TEXT NOT NULL,
  occurred_at INTEGER NOT NULL,
  actor_ref TEXT,
  kind TEXT NOT NULL,
  subject TEXT NOT NULL,
  detail TEXT NOT NULL
);
CREATE INDEX IF NOT EXISTS auth_audit_tenant ON auth_audit (tenant, seq);
