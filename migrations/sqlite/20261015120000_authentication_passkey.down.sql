DROP TABLE IF EXISTS auth_passkey_ceremonies;
DROP TABLE IF EXISTS auth_passkeys;
DROP INDEX IF EXISTS credentials_passkey;
ALTER TABLE auth_credentials DROP COLUMN passkey_id;
