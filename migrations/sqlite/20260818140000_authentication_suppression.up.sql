CREATE TABLE IF NOT EXISTS auth_delivery_records (
  tenant TEXT NOT NULL,
  identity_local TEXT NOT NULL,
  identity_domain TEXT NOT NULL,
  suppressed_by TEXT,
  failures INTEGER NOT NULL,
  first_failure_at INTEGER NOT NULL,
  last_failure_at INTEGER NOT NULL,
  detail TEXT NOT NULL,
  PRIMARY KEY (tenant, identity_local, identity_domain)
);
