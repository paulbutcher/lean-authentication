/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Authentication
import SQLite

/-!
The SQLite backend.

It lives in its own target because the core library depends on no driver (AUTH-2.2). Objects
are prefixed `auth_` so they cannot collide with the client's own, which is what a dedicated
schema does for Postgres (AUTH-15.7.1). Timestamps are epoch integers, which removes a dialect
difference rather than abstracting one (AUTH-15.7.4).

The statements here are written once and shared by both SQL backends in the next stage. That
matters most for the two conditional updates: compare-and-set is exactly where a bug is a
vulnerability, and two independent implementations would be two chances to get it wrong
(AUTH-15.2.2).
-/

namespace Authentication.Sqlite

open SQLite

/-! ## Encoding between domain values and columns -/

private def domainText (d : Domain) : String := d.render

/-- The stored text is what `Domain.render` produced, and a rendered domain has no empty label,
so splitting on the separator recovers the labels it was built from. -/
private def domainOfText (text : String) : Domain := ⟨text.splitOn "."⟩

private def digestBytesText (d : Digest) : String := Codec.Base64Url.encodeString d.bytes

private def digestOf (keyId : String) (bytes : String) : Digest :=
  ⟨⟨keyId⟩, (Codec.Base64Url.decodeString bytes).getD []⟩

private def timeOf (i : Int64) : Timestamp := ⟨i.toInt⟩

private def timeText (t : Timestamp) : Int64 := Int64.ofInt t.epochSeconds

private def phaseText : AttemptPhase → String
  | .pending => "pending"
  | .revealed => "revealed"
  | .completed => "completed"
  | .expired => "expired"
  | .abandoned => "abandoned"

private def phaseOf : String → AttemptPhase
  | "revealed" => .revealed
  | "completed" => .completed
  | "expired" => .expired
  | "abandoned" => .abandoned
  | _ => .pending

private def statusText : AccountStatus → String
  | .active => "active"
  | .deactivated => "deactivated"

private def statusOf (text : String) : AccountStatus :=
  if text == "deactivated" then .deactivated else .active

private def invitationStateText : InvitationState → String
  | .pending => "pending"
  | .accepted => "accepted"
  | .revoked => "revoked"

private def invitationStateOf : String → InvitationState
  | "accepted" => .accepted
  | "revoked" => .revoked
  | _ => .pending

private def actorRef : Actor → Option String
  | .anonymous => none
  | .client reference => some reference

private def actorOf : Option String → Actor
  | none => .anonymous
  | some reference => .client reference

/-! ## Audit events

An audit event is stored as a kind, the identifier it concerns, and a detail. Decoding is
partial only in the sense that a row written by a different version of this table would not be
recognised; every row this backend writes reads back. -/

private def auditColumns {tenant : TenantId} : AuditEvent tenant → String × String × String
  | .attemptCreated attempt => ("attempt-created", attempt.value, "")
  | .linkOpened attempt device =>
    ("link-opened", attempt.value, match device with | .same => "same" | .cross => "cross")
  | .codeEntered attempt outcome =>
    ("code-entered", attempt.value,
      match outcome with
      | .accepted => "accepted"
      | .rejected => "rejected"
      | .budgetExhausted => "budget-exhausted")
  | .attemptAbandoned attempt reason =>
    ("attempt-abandoned", attempt.value,
      match reason with
      | .superseded => "superseded"
      | .codeBudgetExhausted => "code-budget-exhausted")
  | .sessionIssued attempt => ("session-issued", attempt.value, "")
  | .invitationConsumed invitation => ("invitation-consumed", invitation.value, "")
  | .signInRejected outcome =>
    ("sign-in-rejected", "",
      match outcome with
      | .linkSent => "link-sent"
      | .unknownAddress => "unknown-address"
      | .notInvited => "not-invited"
      | .domainNotAllowed => "domain-not-allowed"
      | .addressSuppressed => "address-suppressed"
      | .throttled => "throttled"
      | .malformedAddress => "malformed-address")

private def auditEventOf (tenant : TenantId) (kind subject detail : String) :
    Option (AuditEvent tenant) :=
  match kind with
  | "attempt-created" => some (.attemptCreated ⟨subject⟩)
  | "link-opened" => some (.linkOpened ⟨subject⟩ (if detail == "same" then .same else .cross))
  | "code-entered" =>
    some (.codeEntered ⟨subject⟩
      (if detail == "accepted" then .accepted
        else if detail == "budget-exhausted" then .budgetExhausted
        else .rejected))
  | "attempt-abandoned" =>
    some (.attemptAbandoned ⟨subject⟩
      (if detail == "superseded" then .superseded else .codeBudgetExhausted))
  | "session-issued" => some (.sessionIssued ⟨subject⟩)
  | "invitation-consumed" => some (.invitationConsumed ⟨subject⟩)
  | "sign-in-rejected" =>
    some (.signInRejected
      (if detail == "link-sent" then .linkSent
        else if detail == "unknown-address" then .unknownAddress
        else if detail == "not-invited" then .notInvited
        else if detail == "domain-not-allowed" then .domainNotAllowed
        else if detail == "address-suppressed" then .addressSuppressed
        else if detail == "throttled" then .throttled
        else .malformedAddress))
  | _ => none

/-! ## Rows -/

private structure AccountRow where
  id : String
  identityLocal : String
  identityDomain : String
  sendingLocal : String
  sendingDomain : String
  status : String
  createdAt : Int64
  deriving SQLite.Row

private structure EmailRow where
  localPart : String
  domain : String
  deriving SQLite.Row

private structure AttemptRow where
  id : String
  addressLocal : String
  addressDomain : String
  phase : String
  magicKey : String
  magicBytes : String
  codeKey : String
  codeBytes : String
  emailedKey : Option String
  emailedBytes : Option String
  nonceKey : String
  nonceBytes : String
  failedEntries : Int64
  expiresAt : Int64
  requesterIp : Option String
  requesterAgent : Option String
  requesterLocation : Option String
  deriving SQLite.Row

private structure SessionRow where
  id : String
  accountId : String
  digestKey : String
  digestBytes : String
  createdAt : Int64
  lastSeenAt : Int64
  idleExpiresAt : Int64
  absoluteExpiresAt : Int64
  userAgent : Option String
  location : Option String
  revokedAt : Option Int64
  deriving SQLite.Row

private structure InvitationRow where
  id : String
  addressLocal : String
  addressDomain : String
  tokenKey : String
  tokenBytes : String
  metadata : String
  state : String
  expiresAt : Int64
  createdBy : Option String
  consumedAt : Option Int64
  deriving SQLite.Row

private structure AuditRow where
  occurredAt : Int64
  actorRef : Option String
  kind : String
  subject : String
  detail : String
  deriving SQLite.Row

private structure CountRow where
  count : Int64
  deriving SQLite.Row

/-! ## Schema -/

def createSchema (db : SQLite) : IO Unit := do
  db.exec "
    CREATE TABLE IF NOT EXISTS auth_accounts (
      tenant TEXT NOT NULL,
      id TEXT NOT NULL,
      identity_local TEXT NOT NULL,
      identity_domain TEXT NOT NULL,
      sending_local TEXT NOT NULL,
      sending_domain TEXT NOT NULL,
      status TEXT NOT NULL,
      created_at INTEGER NOT NULL,
      PRIMARY KEY (tenant, id),
      UNIQUE (tenant, identity_local, identity_domain)
    );
    CREATE TABLE IF NOT EXISTS auth_account_emails (
      tenant TEXT NOT NULL,
      account_id TEXT NOT NULL,
      local TEXT NOT NULL,
      domain TEXT NOT NULL,
      PRIMARY KEY (tenant, account_id, local, domain)
    );
    CREATE TABLE IF NOT EXISTS auth_attempts (
      tenant TEXT NOT NULL,
      id TEXT NOT NULL,
      address_local TEXT NOT NULL,
      address_domain TEXT NOT NULL,
      identity_local TEXT NOT NULL,
      identity_domain TEXT NOT NULL,
      phase TEXT NOT NULL,
      magic_key TEXT NOT NULL,
      magic_bytes TEXT NOT NULL,
      code_key TEXT NOT NULL,
      code_bytes TEXT NOT NULL,
      emailed_key TEXT,
      emailed_bytes TEXT,
      nonce_key TEXT NOT NULL,
      nonce_bytes TEXT NOT NULL,
      failed_entries INTEGER NOT NULL,
      expires_at INTEGER NOT NULL,
      requester_ip TEXT,
      requester_agent TEXT,
      requester_location TEXT,
      PRIMARY KEY (tenant, id)
    );
    CREATE UNIQUE INDEX IF NOT EXISTS auth_attempts_live
      ON auth_attempts (tenant, identity_local, identity_domain)
      WHERE phase IN ('pending', 'revealed');
    CREATE TABLE IF NOT EXISTS auth_sessions (
      tenant TEXT NOT NULL,
      id TEXT NOT NULL,
      account_id TEXT NOT NULL,
      digest_key TEXT NOT NULL,
      digest_bytes TEXT NOT NULL,
      created_at INTEGER NOT NULL,
      last_seen_at INTEGER NOT NULL,
      idle_expires_at INTEGER NOT NULL,
      absolute_expires_at INTEGER NOT NULL,
      user_agent TEXT,
      location TEXT,
      revoked_at INTEGER,
      PRIMARY KEY (tenant, id)
    );
    CREATE INDEX IF NOT EXISTS auth_sessions_digest
      ON auth_sessions (tenant, digest_key, digest_bytes);
    CREATE TABLE IF NOT EXISTS auth_invitations (
      tenant TEXT NOT NULL,
      id TEXT NOT NULL,
      address_local TEXT NOT NULL,
      address_domain TEXT NOT NULL,
      token_key TEXT NOT NULL,
      token_bytes TEXT NOT NULL,
      metadata TEXT NOT NULL,
      state TEXT NOT NULL,
      expires_at INTEGER NOT NULL,
      created_by TEXT,
      consumed_at INTEGER,
      PRIMARY KEY (tenant, id)
    );
    CREATE TABLE IF NOT EXISTS auth_audit (
      seq INTEGER PRIMARY KEY AUTOINCREMENT,
      tenant TEXT NOT NULL,
      occurred_at INTEGER NOT NULL,
      actor_ref TEXT,
      kind TEXT NOT NULL,
      subject TEXT NOT NULL,
      detail TEXT NOT NULL
    );
    CREATE INDEX IF NOT EXISTS auth_audit_tenant ON auth_audit (tenant, seq);
  "

/--
Opens an in-memory database with the schema applied. This is what the tests run against, so
they run the statements production runs rather than a parallel implementation (AUTH-16.5).
-/
def openInMemory : IO SQLite := do
  let db ← SQLite.openWith ":memory:" .readWriteCreate
  createSchema db
  pure db

/--
Opens a file-backed database. WAL and a busy timeout are not optional for a SQLite deployment:
without them ordinary concurrent code submissions produce `SQLITE_BUSY` (AUTH-15.8.3).
-/
def openFile (path : System.FilePath) (busyTimeoutMs : Int32 := 5000) : IO SQLite := do
  let db ← SQLite.openWith path .readWriteCreate (busyTimeoutMs := busyTimeoutMs)
  db.exec "PRAGMA journal_mode=WAL"
  createSchema db
  pure db

/-! ## Operations -/

private def readAccount {tenant : TenantId} (db : SQLite) (row : AccountRow) :
    IO (Account tenant) := do
  let emails ← (← db query!"
      SELECT local, domain FROM auth_account_emails
      WHERE tenant = {tenant.value} AND account_id = {row.id}" as EmailRow).toArray
  pure
    { id := ⟨row.id⟩
      identity := ⟨row.identityLocal, domainOfText row.identityDomain⟩
      primaryEmail := ⟨row.sendingLocal, domainOfText row.sendingDomain⟩
      additionalEmails := (emails.map fun e => ⟨e.localPart, domainOfText e.domain⟩).toList
      status := statusOf row.status
      createdAt := timeOf row.createdAt }

private def accountByIdentity (db : SQLite) (tenant : TenantId) (identity : NormalisedEmail) :
    IO (Option (Account tenant)) := do
  let rows ← (← db query!"
      SELECT id, identity_local, identity_domain, sending_local, sending_domain, status, created_at
      FROM auth_accounts
      WHERE tenant = {tenant.value} AND identity_local = {identity.localPart}
        AND identity_domain = {domainText identity.domain}" as AccountRow).toArray
  match rows[0]? with
  | none => pure none
  | some row => some <$> readAccount db row

private def createAccount (db : SQLite) (tenant : TenantId) (account : Account tenant) :
    IO (Except StoreError (AccountCreated tenant)) :=
  db.transaction do
    let inserted ←
      try
        db exec!"
          INSERT INTO auth_accounts
            (tenant, id, identity_local, identity_domain, sending_local, sending_domain,
             status, created_at)
          VALUES ({tenant.value}, {account.id.value}, {account.identity.localPart},
            {domainText account.identity.domain}, {account.primaryEmail.localPart},
            {domainText account.primaryEmail.domain}, {statusText account.status},
            {timeText account.createdAt})"
        pure true
      catch _ => pure false
    if !inserted then
      return .error .duplicateAccount
    for email in account.additionalEmails do
      db exec!"
        INSERT OR IGNORE INTO auth_account_emails (tenant, account_id, local, domain)
        VALUES ({tenant.value}, {account.id.value}, {email.localPart}, {domainText email.domain})"
    let counted ← (← db query!"
        SELECT COUNT(*) FROM auth_accounts WHERE tenant = {tenant.value}" as CountRow).toArray
    let total := (counted[0]?.map (·.count)).getD (0 : Int64)
    pure (.ok { account, firstInTenant := total == 1 })

private def readAttempt {tenant : TenantId} (row : AttemptRow) : AttemptState tenant :=
  { id := ⟨row.id⟩
    address := ⟨row.addressLocal, domainOfText row.addressDomain⟩
    phase := phaseOf row.phase
    magicToken := digestOf row.magicKey row.magicBytes
    revealedCode := digestOf row.codeKey row.codeBytes
    emailedCode :=
      match row.emailedKey, row.emailedBytes with
      | some k, some b => some (digestOf k b)
      | _, _ => none
    bindingNonce := digestOf row.nonceKey row.nonceBytes
    failedCodeEntries := row.failedEntries.toNatClampNeg
    expiresAt := timeOf row.expiresAt
    requester :=
      { ip := row.requesterIp
        userAgent := row.requesterAgent
        approximateLocation := row.requesterLocation } }

private def attemptById (db : SQLite) (tenant : TenantId) (id : AttemptId tenant) :
    IO (Option (AttemptState tenant)) := do
  let rows ← (← db query!"
      SELECT id, address_local, address_domain, phase, magic_key, magic_bytes, code_key,
        code_bytes, emailed_key, emailed_bytes, nonce_key, nonce_bytes, failed_entries,
        expires_at, requester_ip, requester_agent, requester_location
      FROM auth_attempts
      WHERE tenant = {tenant.value} AND id = {id.value}" as AttemptRow).toArray
  pure (rows[0]?.map readAttempt)

private structure IdRow where
  id : String
  deriving SQLite.Row

private def startAttempt (db : SQLite) (tenant : TenantId) (attempt : AttemptState tenant) :
    IO (List (AttemptId tenant)) :=
  db.transaction do
    let identity := attempt.address.normalise
    let live ← (← db query!"
        SELECT id FROM auth_attempts
        WHERE tenant = {tenant.value} AND identity_local = {identity.localPart}
          AND identity_domain = {domainText identity.domain}
          AND phase IN ('pending', 'revealed')" as IdRow).toArray
    db exec!"
      UPDATE auth_attempts SET phase = 'abandoned'
      WHERE tenant = {tenant.value} AND identity_local = {identity.localPart}
        AND identity_domain = {domainText identity.domain}
        AND phase IN ('pending', 'revealed')"
    db exec!"
      INSERT INTO auth_attempts
        (tenant, id, address_local, address_domain, identity_local, identity_domain, phase,
         magic_key, magic_bytes, code_key, code_bytes, emailed_key, emailed_bytes, nonce_key,
         nonce_bytes, failed_entries, expires_at, requester_ip, requester_agent,
         requester_location)
      VALUES ({tenant.value}, {attempt.id.value}, {attempt.address.localPart},
        {domainText attempt.address.domain}, {identity.localPart},
        {domainText identity.domain}, {phaseText attempt.phase},
        {attempt.magicToken.keyId.value}, {digestBytesText attempt.magicToken},
        {attempt.revealedCode.keyId.value}, {digestBytesText attempt.revealedCode},
        {attempt.emailedCode.map (·.keyId.value)},
        {attempt.emailedCode.map digestBytesText},
        {attempt.bindingNonce.keyId.value}, {digestBytesText attempt.bindingNonce},
        {Int64.ofNat attempt.failedCodeEntries}, {timeText attempt.expiresAt},
        {attempt.requester.ip}, {attempt.requester.userAgent},
        {attempt.requester.approximateLocation})"
    pure ((live.map fun r => (⟨r.id⟩ : AttemptId tenant)).toList)

/-- The condition names the phase and the failed-entry count the caller believed it was acting
on. Anything that changed either of them since the read wins, and this update reports that it
did not happen (AUTH-15.4.1). -/
private def commitAttempt (db : SQLite) (tenant : TenantId) (expected next : AttemptState tenant) :
    IO Bool := do
  db exec!"
    UPDATE auth_attempts
    SET phase = {phaseText next.phase}, failed_entries = {Int64.ofNat next.failedCodeEntries}
    WHERE tenant = {tenant.value} AND id = {expected.id.value}
      AND phase = {phaseText expected.phase}
      AND failed_entries = {Int64.ofNat expected.failedCodeEntries}"
  pure ((← db.changes) == 1)

private def readSession {tenant : TenantId} (row : SessionRow) : Session tenant :=
  { id := ⟨row.id⟩
    account := ⟨row.accountId⟩
    identifierDigest := digestOf row.digestKey row.digestBytes
    createdAt := timeOf row.createdAt
    lastSeenAt := timeOf row.lastSeenAt
    idleExpiresAt := timeOf row.idleExpiresAt
    absoluteExpiresAt := timeOf row.absoluteExpiresAt
    userAgent := row.userAgent
    approximateLocation := row.location
    revokedAt := row.revokedAt.map timeOf }

private def createSession (db : SQLite) (tenant : TenantId) (session : Session tenant) :
    IO Unit :=
  db exec!"
    INSERT INTO auth_sessions
      (tenant, id, account_id, digest_key, digest_bytes, created_at, last_seen_at,
       idle_expires_at, absolute_expires_at, user_agent, location, revoked_at)
    VALUES ({tenant.value}, {session.id.value}, {session.account.value},
      {session.identifierDigest.keyId.value}, {digestBytesText session.identifierDigest},
      {timeText session.createdAt}, {timeText session.lastSeenAt},
      {timeText session.idleExpiresAt}, {timeText session.absoluteExpiresAt},
      {session.userAgent}, {session.approximateLocation},
      {session.revokedAt.map timeText})"

private def sessionColumns : String :=
  "SELECT id, account_id, digest_key, digest_bytes, created_at, last_seen_at, idle_expires_at,
     absolute_expires_at, user_agent, location, revoked_at FROM auth_sessions"

private def sessionByDigest (db : SQLite) (tenant : TenantId) (now : Timestamp) (digest : Digest) :
    IO (Option (Session tenant)) := do
  let rows ← (← db query!"
      SELECT id, account_id, digest_key, digest_bytes, created_at, last_seen_at,
        idle_expires_at, absolute_expires_at, user_agent, location, revoked_at
      FROM auth_sessions
      WHERE tenant = {tenant.value} AND digest_key = {digest.keyId.value}
        AND digest_bytes = {digestBytesText digest}
        AND revoked_at IS NULL AND idle_expires_at > {timeText now}
        AND absolute_expires_at > {timeText now}" as SessionRow).toArray
  pure (rows[0]?.map readSession)

private def sessionsForAccount (db : SQLite) (tenant : TenantId) (now : Timestamp)
    (account : AccountId tenant) : IO (List (Session tenant)) := do
  let rows ← (← db query!"
      SELECT id, account_id, digest_key, digest_bytes, created_at, last_seen_at,
        idle_expires_at, absolute_expires_at, user_agent, location, revoked_at
      FROM auth_sessions
      WHERE tenant = {tenant.value} AND account_id = {account.value}
        AND revoked_at IS NULL AND idle_expires_at > {timeText now}
        AND absolute_expires_at > {timeText now}" as SessionRow).toArray
  pure (rows.map readSession).toList

private def revokeSession (db : SQLite) (tenant : TenantId) (now : Timestamp)
    (id : SessionId tenant) : IO Unit :=
  db exec!"
    UPDATE auth_sessions SET revoked_at = {timeText now}
    WHERE tenant = {tenant.value} AND id = {id.value} AND revoked_at IS NULL"

private def revokeSessionsForAccount (db : SQLite) (tenant : TenantId) (now : Timestamp)
    (account : AccountId tenant) : IO Unit :=
  db exec!"
    UPDATE auth_sessions SET revoked_at = {timeText now}
    WHERE tenant = {tenant.value} AND account_id = {account.value} AND revoked_at IS NULL"

private def readInvitation {tenant : TenantId} (row : InvitationRow) : Invitation tenant :=
  { id := ⟨row.id⟩
    address := ⟨row.addressLocal, domainOfText row.addressDomain⟩
    tokenDigest := digestOf row.tokenKey row.tokenBytes
    metadata := ⟨row.metadata⟩
    state := invitationStateOf row.state
    expiresAt := timeOf row.expiresAt
    createdBy := actorOf row.createdBy
    consumedAt := row.consumedAt.map timeOf }

private def createInvitation (db : SQLite) (tenant : TenantId) (invitation : Invitation tenant) :
    IO Unit :=
  db exec!"
    INSERT INTO auth_invitations
      (tenant, id, address_local, address_domain, token_key, token_bytes, metadata, state,
       expires_at, created_by, consumed_at)
    VALUES ({tenant.value}, {invitation.id.value}, {invitation.address.localPart},
      {domainText invitation.address.domain}, {invitation.tokenDigest.keyId.value},
      {digestBytesText invitation.tokenDigest}, {invitation.metadata.payload},
      {invitationStateText invitation.state}, {timeText invitation.expiresAt},
      {actorRef invitation.createdBy}, {invitation.consumedAt.map timeText})"

private def invitationById (db : SQLite) (tenant : TenantId) (id : InvitationId tenant) :
    IO (Option (Invitation tenant)) := do
  let rows ← (← db query!"
      SELECT id, address_local, address_domain, token_key, token_bytes, metadata, state,
        expires_at, created_by, consumed_at
      FROM auth_invitations
      WHERE tenant = {tenant.value} AND id = {id.value}" as InvitationRow).toArray
  pure (rows[0]?.map readInvitation)

private def commitInvitation (db : SQLite) (tenant : TenantId) (expected next : Invitation tenant) :
    IO Bool := do
  db exec!"
    UPDATE auth_invitations
    SET state = {invitationStateText next.state}, consumed_at = {next.consumedAt.map timeText}
    WHERE tenant = {tenant.value} AND id = {expected.id.value}
      AND state = {invitationStateText expected.state}"
  pure ((← db.changes) == 1)

private def invitationsForTenant (db : SQLite) (tenant : TenantId) :
    IO (List (Invitation tenant)) := do
  let rows ← (← db query!"
      SELECT id, address_local, address_domain, token_key, token_bytes, metadata, state,
        expires_at, created_by, consumed_at
      FROM auth_invitations WHERE tenant = {tenant.value}" as InvitationRow).toArray
  pure (rows.map readInvitation).toList

private def appendAudit (db : SQLite) (tenant : TenantId) (entry : AuditEntry tenant) : IO Unit :=
  let (kind, subject, detail) := auditColumns entry.event
  db exec!"
    INSERT INTO auth_audit (tenant, occurred_at, actor_ref, kind, subject, detail)
    VALUES ({tenant.value}, {timeText entry.occurredAt}, {actorRef entry.actor}, {kind},
      {subject}, {detail})"

private def auditEntries (db : SQLite) (tenant : TenantId) : IO (List (AuditEntry tenant)) := do
  let rows ← (← db query!"
      SELECT occurred_at, actor_ref, kind, subject, detail
      FROM auth_audit WHERE tenant = {tenant.value} ORDER BY seq" as AuditRow).toArray
  pure (rows.toList.filterMap fun row =>
    (auditEventOf tenant row.kind row.subject row.detail).map fun event =>
      { occurredAt := timeOf row.occurredAt, actor := actorOf row.actorRef, event })

private def deleteTenant (db : SQLite) (tenant : TenantId) : IO Unit :=
  db.transaction do
    db exec!"DELETE FROM auth_account_emails WHERE tenant = {tenant.value}"
    db exec!"DELETE FROM auth_accounts WHERE tenant = {tenant.value}"
    db exec!"DELETE FROM auth_attempts WHERE tenant = {tenant.value}"
    db exec!"DELETE FROM auth_sessions WHERE tenant = {tenant.value}"
    db exec!"DELETE FROM auth_invitations WHERE tenant = {tenant.value}"
    db exec!"DELETE FROM auth_audit WHERE tenant = {tenant.value}"

/-- The port, wired to one connection. -/
def store (db : SQLite) : AuthStore IO :=
  { accountByIdentity := accountByIdentity db
    createAccount := createAccount db
    startAttempt := startAttempt db
    attemptById := attemptById db
    commitAttempt := commitAttempt db
    createSession := createSession db
    sessionByDigest := sessionByDigest db
    sessionsForAccount := sessionsForAccount db
    revokeSession := revokeSession db
    revokeSessionsForAccount := revokeSessionsForAccount db
    createInvitation := createInvitation db
    invitationById := invitationById db
    commitInvitation := commitInvitation db
    invitationsForTenant := invitationsForTenant db
    appendAudit := appendAudit db
    auditEntries := auditEntries db
    deleteTenant := deleteTenant db }

/--
The transactional capability (AUTH-15.3). SQLite has no nested transactions, so the block runs
against the same connection: a client that takes this capability accepts that the library's
tables live in its own database (AUTH-15.3.5).
-/
def transactionalStore (db : SQLite) : TransactionalStore IO :=
  { store := store db
    runInTx := fun action => db.transaction (action (store db)) }

end Authentication.Sqlite
