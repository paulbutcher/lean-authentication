CREATE TABLE IF NOT EXISTS auth_rate_counters (
  scope_key TEXT NOT NULL,
  action TEXT NOT NULL,
  bucket INTEGER NOT NULL,
  uses INTEGER NOT NULL,
  PRIMARY KEY (scope_key, action, bucket)
);
