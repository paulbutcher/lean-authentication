ALTER TABLE auth.passkey_ceremonies ADD COLUMN IF NOT EXISTS recovery_grant_id text;
ALTER TABLE auth.federation_states ADD COLUMN IF NOT EXISTS recovery_grant_id text;
