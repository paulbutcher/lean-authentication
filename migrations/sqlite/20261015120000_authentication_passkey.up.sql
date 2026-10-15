ALTER TABLE auth_credentials ADD COLUMN passkey_id text;
CREATE UNIQUE INDEX IF NOT EXISTS credentials_passkey
  ON auth_credentials (tenant, passkey_id) WHERE kind = 'passkey';
CREATE TABLE IF NOT EXISTS auth_passkeys (
  tenant text NOT NULL,
  credential_id text NOT NULL,
  public_key text NOT NULL,
  algorithm integer NOT NULL,
  sign_count integer NOT NULL,
  transports text NOT NULL,
  aaguid text NOT NULL,
  backup_eligible integer NOT NULL,
  backup_state integer NOT NULL,
  label text NOT NULL,
  created_at integer NOT NULL,
  PRIMARY KEY (tenant, credential_id)
);
CREATE TABLE IF NOT EXISTS auth_passkey_ceremonies (
  tenant text NOT NULL,
  id text NOT NULL,
  kind text NOT NULL,
  challenge_key text NOT NULL,
  challenge_bytes text NOT NULL,
  nonce_key text NOT NULL,
  nonce_bytes text NOT NULL,
  account_id text,
  return_to text,
  created_at integer NOT NULL,
  expires_at integer NOT NULL,
  consumed_at integer,
  PRIMARY KEY (tenant, id)
);
