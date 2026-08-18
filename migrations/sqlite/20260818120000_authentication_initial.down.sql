-- SQLite has no schemas, so the tables are dropped by name. Their indexes go with them.
DROP TABLE IF EXISTS auth_audit;
DROP TABLE IF EXISTS auth_invitations;
DROP TABLE IF EXISTS auth_sessions;
DROP TABLE IF EXISTS auth_attempts;
DROP TABLE IF EXISTS auth_account_emails;
DROP TABLE IF EXISTS auth_accounts;
