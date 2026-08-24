CREATE TABLE IF NOT EXISTS auth_oauth_clients (
  tenant TEXT NOT NULL,
  id TEXT NOT NULL,
  metadata TEXT NOT NULL,
  registered_at INTEGER NOT NULL,
  last_used_at INTEGER NOT NULL,
  PRIMARY KEY (tenant, id)
);
CREATE INDEX IF NOT EXISTS auth_oauth_clients_idle ON auth_oauth_clients (tenant, last_used_at);
CREATE TABLE IF NOT EXISTS auth_oauth_documents (
  tenant TEXT NOT NULL,
  client_id TEXT NOT NULL,
  metadata TEXT NOT NULL,
  fetched_at INTEGER NOT NULL,
  fresh_until INTEGER NOT NULL,
  PRIMARY KEY (tenant, client_id)
);
CREATE TABLE IF NOT EXISTS auth_oauth_codes (
  tenant TEXT NOT NULL,
  digest_key TEXT NOT NULL,
  digest_bytes TEXT NOT NULL,
  grant_id TEXT NOT NULL,
  account_id TEXT NOT NULL,
  client_id TEXT NOT NULL,
  redirect_uri TEXT NOT NULL,
  redirect_uri_given INTEGER NOT NULL,
  code_challenge TEXT NOT NULL,
  resource TEXT NOT NULL,
  scopes TEXT NOT NULL,
  issued_at INTEGER NOT NULL,
  expires_at INTEGER NOT NULL,
  redeemed_at INTEGER,
  PRIMARY KEY (tenant, digest_key, digest_bytes)
);
CREATE INDEX IF NOT EXISTS auth_oauth_codes_grant ON auth_oauth_codes (tenant, grant_id);
CREATE TABLE IF NOT EXISTS auth_oauth_access_tokens (
  tenant TEXT NOT NULL,
  digest_key TEXT NOT NULL,
  digest_bytes TEXT NOT NULL,
  grant_id TEXT NOT NULL,
  account_id TEXT NOT NULL,
  client_id TEXT NOT NULL,
  resource TEXT NOT NULL,
  scopes TEXT NOT NULL,
  issued_at INTEGER NOT NULL,
  expires_at INTEGER NOT NULL,
  revoked_at INTEGER,
  PRIMARY KEY (tenant, digest_key, digest_bytes)
);
CREATE INDEX IF NOT EXISTS auth_oauth_access_tokens_grant ON auth_oauth_access_tokens (tenant, grant_id);
CREATE INDEX IF NOT EXISTS auth_oauth_access_tokens_holder
  ON auth_oauth_access_tokens (tenant, account_id, client_id);
CREATE TABLE IF NOT EXISTS auth_oauth_refresh_tokens (
  tenant TEXT NOT NULL,
  digest_key TEXT NOT NULL,
  digest_bytes TEXT NOT NULL,
  grant_id TEXT NOT NULL,
  account_id TEXT NOT NULL,
  client_id TEXT NOT NULL,
  resource TEXT NOT NULL,
  scopes TEXT NOT NULL,
  issued_at INTEGER NOT NULL,
  expires_at INTEGER NOT NULL,
  replaced_at INTEGER,
  revoked_at INTEGER,
  PRIMARY KEY (tenant, digest_key, digest_bytes)
);
CREATE INDEX IF NOT EXISTS auth_oauth_refresh_tokens_grant
  ON auth_oauth_refresh_tokens (tenant, grant_id);
CREATE INDEX IF NOT EXISTS auth_oauth_refresh_tokens_holder
  ON auth_oauth_refresh_tokens (tenant, account_id, client_id);
