DROP TABLE IF EXISTS auth.passkey_ceremonies;
DROP TABLE IF EXISTS auth.passkeys;
DROP INDEX IF EXISTS auth.credentials_passkey;
ALTER TABLE auth.credentials DROP COLUMN passkey_id;
