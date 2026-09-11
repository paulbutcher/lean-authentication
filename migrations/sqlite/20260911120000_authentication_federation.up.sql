CREATE TABLE IF NOT EXISTS auth_credentials (
  tenant text NOT NULL,
  id text NOT NULL,
  account_id text NOT NULL,
  kind text NOT NULL,
  issuer text,
  subject text,
  local text,
  domain text,
  created_at integer NOT NULL,
  PRIMARY KEY (tenant, id)
);
CREATE UNIQUE INDEX IF NOT EXISTS credentials_identity
  ON auth_credentials (tenant, issuer, subject) WHERE kind = 'federated';
CREATE INDEX IF NOT EXISTS credentials_account ON auth_credentials (tenant, account_id);
CREATE UNIQUE INDEX IF NOT EXISTS account_emails_address
  ON auth_account_emails (tenant, local, domain);
CREATE TABLE IF NOT EXISTS auth_federation_states (
  tenant text NOT NULL,
  id text NOT NULL,
  provider text NOT NULL,
  digest_key text NOT NULL,
  digest_bytes text NOT NULL,
  verifier text NOT NULL,
  nonce text NOT NULL,
  return_to text,
  created_at integer NOT NULL,
  expires_at integer NOT NULL,
  consumed_at integer,
  PRIMARY KEY (tenant, id)
);
CREATE INDEX IF NOT EXISTS federation_states_digest
  ON auth_federation_states (tenant, digest_key, digest_bytes);
