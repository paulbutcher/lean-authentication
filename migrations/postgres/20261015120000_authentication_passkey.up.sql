ALTER TABLE auth.credentials ADD COLUMN IF NOT EXISTS passkey_id text;
CREATE UNIQUE INDEX IF NOT EXISTS credentials_passkey
  ON auth.credentials (tenant, passkey_id) WHERE kind = 'passkey';
CREATE TABLE IF NOT EXISTS auth.passkeys (
  tenant text NOT NULL,
  credential_id text NOT NULL,
  public_key text NOT NULL,
  algorithm bigint NOT NULL,
  sign_count bigint NOT NULL,
  transports text NOT NULL,
  aaguid text NOT NULL,
  backup_eligible bigint NOT NULL,
  backup_state bigint NOT NULL,
  label text NOT NULL,
  created_at bigint NOT NULL,
  PRIMARY KEY (tenant, credential_id)
);
CREATE TABLE IF NOT EXISTS auth.passkey_ceremonies (
  tenant text NOT NULL,
  id text NOT NULL,
  kind text NOT NULL,
  challenge_key text NOT NULL,
  challenge_bytes text NOT NULL,
  nonce_key text NOT NULL,
  nonce_bytes text NOT NULL,
  account_id text,
  return_to text,
  created_at bigint NOT NULL,
  expires_at bigint NOT NULL,
  consumed_at bigint,
  PRIMARY KEY (tenant, id)
);
