CREATE TABLE IF NOT EXISTS auth.recovery_grants (
  tenant text NOT NULL,
  id text NOT NULL,
  account_id text NOT NULL,
  token_key text NOT NULL,
  token_bytes text NOT NULL,
  disposition text NOT NULL,
  state text NOT NULL,
  expires_at bigint NOT NULL,
  created_by text,
  spent_at bigint,
  PRIMARY KEY (tenant, id)
);
CREATE INDEX IF NOT EXISTS recovery_grants_account
  ON auth.recovery_grants (tenant, account_id);
