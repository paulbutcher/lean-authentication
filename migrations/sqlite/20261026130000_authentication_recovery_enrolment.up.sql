ALTER TABLE auth_passkey_ceremonies ADD COLUMN recovery_grant_id text;
ALTER TABLE auth_federation_states ADD COLUMN recovery_grant_id text;
