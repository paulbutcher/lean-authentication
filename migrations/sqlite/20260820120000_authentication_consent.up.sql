CREATE TABLE IF NOT EXISTS auth_consents (
  seq INTEGER PRIMARY KEY AUTOINCREMENT,
  tenant TEXT NOT NULL,
  account TEXT NOT NULL,
  subject TEXT NOT NULL,
  version TEXT NOT NULL,
  act TEXT NOT NULL,
  recorded_at INTEGER NOT NULL
);
CREATE INDEX IF NOT EXISTS auth_consents_account ON auth_consents (tenant, account, seq);
CREATE INDEX IF NOT EXISTS auth_consents_subject ON auth_consents (tenant, subject, seq);
