/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Authentication
public import AuthenticationSql.Connection

/-!
One implementation of `AuthStore` for every SQL backend (AUTH-15.2.2).

The statements live here rather than in each backend because compare-and-set is where a bug is
a vulnerability, and two independent implementations would be two independent chances to get it
wrong. What a backend still owns is its schema and migrations (AUTH-15.7.1), its dialect, and
the driver adapter; none of those can change what a conditional update tests.

Timestamps are epoch integers throughout, which removes a dialect difference rather than
abstracting one (AUTH-15.7.4).
-/

public section

namespace Authentication.Sql

private def accounts : TableName := ⟨"accounts"⟩
private def accountEmails : TableName := ⟨"account_emails"⟩
private def attempts : TableName := ⟨"attempts"⟩
private def sessions : TableName := ⟨"sessions"⟩
private def invitations : TableName := ⟨"invitations"⟩
private def deliveryRecords : TableName := ⟨"delivery_records"⟩
private def consents : TableName := ⟨"consents"⟩
private def audit : TableName := ⟨"audit"⟩

/-- The tables these statements read and write, as the bare names `Dialect.table` qualifies. A
backend's schema has to create all of them and nothing here depends on what it calls them. -/
def tableNames : List String :=
  [accounts.value, accountEmails.value, attempts.value, sessions.value, invitations.value,
    deliveryRecords.value, consents.value, audit.value]

/-! ## Encoding between domain values and columns -/

private def domainText (d : Domain) : String := d.render

/-- The stored text is what `Domain.render` produced, and a rendered domain has no empty label,
so splitting on the separator recovers the labels it was built from. -/
private def domainOfText (text : String) : Domain := ⟨text.splitOn "."⟩

private def digestBytesText (d : Digest) : String := Codec.Base64Url.encodeString d.bytes

private def digestOf (keyId : String) (bytes : String) : Digest :=
  ⟨⟨keyId⟩, (Codec.Base64Url.decodeString bytes).getD ⟨#[]⟩⟩

private def timeOf (i : Int) : Timestamp := ⟨i⟩

private def timeText (t : Timestamp) : Int := t.epochSeconds

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

private def suppressionText : SuppressionReason → String
  | .hardBounce => "hard-bounce"
  | .spamComplaint => "spam-complaint"
  | .client => "client"

private def suppressionOf : String → SuppressionReason
  | "spam-complaint" => .spamComplaint
  | "client" => .client
  | _ => .hardBounce

private def consentActText : ConsentAct → String
  | .granted => "granted"
  | .withdrawn => "withdrawn"

private def consentActOf : String → ConsentAct
  | "withdrawn" => .withdrawn
  | _ => .granted

private def normalisedText (address : NormalisedEmail) : String :=
  address.localPart ++ "@" ++ domainText address.domain

/-- A normalised address is already folded and its local part keeps whatever quoting it had, so
what `normalisedText` wrote is what the parser accepts back. -/
private def normalisedOf (text : String) : Option NormalisedEmail :=
  (EmailAddress.parse text).toOption.map (·.normalise)

/-! ## Audit events

An audit event is stored as a kind, the identifier it concerns, and a detail. Decoding is
partial only in the sense that a row written by a different version of this table would not be
recognised; every row this implementation writes reads back. -/

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
      | .accountDeactivated => "account-deactivated"
      | .throttled => "throttled"
      | .malformedAddress => "malformed-address")
  | .sessionRevoked session => ("session-revoked", session.value, "")
  | .accountSessionsRevoked account reason =>
    ("account-sessions-revoked", account.value,
      match reason with
      | .requested => "requested"
      | .primaryEmailChanged => "primary-email-changed"
      | .accountDeactivated => "account-deactivated"
      | .recovery => "recovery")
  | .primaryEmailChanged account => ("primary-email-changed", account.value, "")
  | .accountDeactivated account => ("account-deactivated", account.value, "")
  | .accountReactivated account => ("account-reactivated", account.value, "")
  | .addressSuppressed address reason =>
    ("address-suppressed", normalisedText address,
      suppressionText reason)
  | .suppressionCleared address =>
    ("suppression-cleared", normalisedText address, "")
  | .consentGranted account subject => ("consent-granted", account.value, subject.name)
  | .consentWithdrawn account subject => ("consent-withdrawn", account.value, subject.name)

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
        else if detail == "account-deactivated" then .accountDeactivated
        else if detail == "throttled" then .throttled
        else .malformedAddress))
  | "session-revoked" => some (.sessionRevoked ⟨subject⟩)
  | "account-sessions-revoked" =>
    some (.accountSessionsRevoked ⟨subject⟩
      (if detail == "primary-email-changed" then .primaryEmailChanged
        else if detail == "account-deactivated" then .accountDeactivated
        else if detail == "recovery" then .recovery
        else .requested))
  | "primary-email-changed" => some (.primaryEmailChanged ⟨subject⟩)
  | "account-deactivated" => some (.accountDeactivated ⟨subject⟩)
  | "account-reactivated" => some (.accountReactivated ⟨subject⟩)
  | "address-suppressed" =>
    (normalisedOf subject).map fun address => .addressSuppressed address (suppressionOf detail)
  | "suppression-cleared" => (normalisedOf subject).map (.suppressionCleared ·)
  | "consent-granted" => some (.consentGranted ⟨subject⟩ ⟨detail⟩)
  | "consent-withdrawn" => some (.consentWithdrawn ⟨subject⟩ ⟨detail⟩)
  | _ => none

/-! ## Running statements -/

variable {m : Type → Type}

private structure Ctx (m : Type → Type) where
  dialect : Dialect
  conn : SqlConnection m

private def Ctx.rows [Monad m] (c : Ctx m) (s : Statement) : m (Array SqlRow) :=
  c.conn.rows c.dialect s

private def Ctx.first [Monad m] (c : Ctx m) (s : Statement) : m (Option SqlRow) :=
  c.conn.first c.dialect s

private def Ctx.affected [Monad m] (c : Ctx m) (s : Statement) : m Nat :=
  c.conn.affected c.dialect s

private def Ctx.run [Monad m] (c : Ctx m) (s : Statement) : m Unit := do
  discard (c.affected s)

/-- The statements inside run on the connection the transaction is open on rather than on the one
this was reached through, which for a pooled driver are not the same. The block's `c` shadows the
outer one so that reaching the wrong connection is not expressible. -/
private def Ctx.transaction [Monad m] {α : Type} (c : Ctx m) (action : Ctx m → m α) : m α :=
  c.conn.transaction fun conn => action { c with conn }

/-! ## Accounts -/

private def accountSelect : Statement :=
  sql!"SELECT id, identity_local, identity_domain, sending_local, sending_domain, status,
         created_at
       FROM {accounts}"

private def readAccount [Monad m] {tenant : TenantId} (c : Ctx m) (row : SqlRow) :
    m (Account tenant) := do
  let id := row.text 0
  let emails ← c.rows
    sql!"SELECT local, domain FROM {accountEmails}
         WHERE tenant = {tenant.value} AND account_id = {id}"
  pure
    { id := ⟨id⟩
      identity := ⟨row.text 1, domainOfText (row.text 2)⟩
      primaryEmail := ⟨row.text 3, domainOfText (row.text 4)⟩
      additionalEmails := (emails.map fun e => ⟨e.text 0, domainOfText (e.text 1)⟩).toList
      status := statusOf (row.text 5)
      createdAt := timeOf (row.int 6) }

private def accountByIdentity [Monad m] (c : Ctx m) (tenant : TenantId)
    (identity : NormalisedEmail) : m (Option (Account tenant)) := do
  let row ← c.first (accountSelect ++
    sql!" WHERE tenant = {tenant.value} AND identity_local = {identity.localPart}
            AND identity_domain = {domainText identity.domain}")
  match row with
  | none => pure none
  | some row => some <$> readAccount c row

private def accountById [Monad m] (c : Ctx m) (tenant : TenantId) (id : AccountId tenant) :
    m (Option (Account tenant)) := do
  let row ← c.first (accountSelect ++ sql!" WHERE tenant = {tenant.value} AND id = {id.value}")
  match row with
  | none => pure none
  | some row => some <$> readAccount c row

/-- An `UPDATE` cannot say `ON CONFLICT`, so the collision is looked for first and inside the
transaction. The unique index is still what enforces uniqueness; the lookup is what turns the
case a client will actually hit into a typed error rather than a driver exception. -/
private def setPrimaryEmail [Monad m] (c : Ctx m) (tenant : TenantId) (id : AccountId tenant)
    (address : EmailAddress) : m (Except StoreError Unit) :=
  c.transaction fun c => do
    let identity := address.normalise
    let holder ← c.first
      sql!"SELECT id FROM {accounts}
           WHERE tenant = {tenant.value} AND identity_local = {identity.localPart}
             AND identity_domain = {domainText identity.domain}"
    match holder.map (·.text 0) with
    | some existing =>
      if existing != id.value then return .error .duplicateAccount
    | none => pure ()
    let affected ← c.affected
      sql!"UPDATE {accounts}
           SET identity_local = {identity.localPart},
             identity_domain = {domainText identity.domain},
             sending_local = {address.localPart},
             sending_domain = {domainText address.domain}
           WHERE tenant = {tenant.value} AND id = {id.value}"
    pure (if affected == 1 then .ok () else .error .unknownAccount)

private def setAccountStatus [Monad m] (c : Ctx m) (tenant : TenantId) (id : AccountId tenant)
    (status : AccountStatus) : m (Except StoreError Unit) := do
  let affected ← c.affected
    sql!"UPDATE {accounts} SET status = {statusText status}
         WHERE tenant = {tenant.value} AND id = {id.value}"
  pure (if affected == 1 then .ok () else .error .unknownAccount)

/-- `ON CONFLICT DO NOTHING` and a row count is how the duplicate is detected, because it is one
statement: a caller that selects first and inserts second races, and the race is the duplicate
account (AUTH-15.4.2). -/
private def createAccount [Monad m] (c : Ctx m) (tenant : TenantId) (account : Account tenant) :
    m (Except StoreError (AccountCreated tenant)) :=
  c.transaction fun c => do
    let inserted ← c.affected
      sql!"INSERT INTO {accounts}
             (tenant, id, identity_local, identity_domain, sending_local, sending_domain,
              status, created_at)
           VALUES ({tenant.value}, {account.id.value}, {account.identity.localPart},
             {domainText account.identity.domain}, {account.primaryEmail.localPart},
             {domainText account.primaryEmail.domain}, {statusText account.status},
             {timeText account.createdAt})
           ON CONFLICT DO NOTHING"
    if inserted == 0 then
      return .error .duplicateAccount
    for email in account.additionalEmails do
      c.run
        sql!"INSERT INTO {accountEmails} (tenant, account_id, local, domain)
             VALUES ({tenant.value}, {account.id.value}, {email.localPart},
               {domainText email.domain})
             ON CONFLICT DO NOTHING"
    let counted ← c.first sql!"SELECT COUNT(*) FROM {accounts} WHERE tenant = {tenant.value}"
    pure (.ok { account, firstInTenant := (counted.map (·.int 0)).getD 0 == 1 })

/-! ## Attempts -/

private def attemptSelect : Statement :=
  sql!"SELECT id, address_local, address_domain, phase, magic_key, magic_bytes, code_key,
         code_bytes, emailed_key, emailed_bytes, nonce_key, nonce_bytes, failed_entries,
         expires_at, requester_ip, requester_agent, requester_location, invitation_id
       FROM {attempts}"

private def readAttempt {tenant : TenantId} (row : SqlRow) : AttemptState tenant :=
  { id := ⟨row.text 0⟩
    address := ⟨row.text 1, domainOfText (row.text 2)⟩
    phase := phaseOf (row.text 3)
    magicToken := digestOf (row.text 4) (row.text 5)
    revealedCode := digestOf (row.text 6) (row.text 7)
    emailedCode :=
      match row.text? 8, row.text? 9 with
      | some k, some b => some (digestOf k b)
      | _, _ => none
    bindingNonce := digestOf (row.text 10) (row.text 11)
    failedCodeEntries := row.nat 12
    expiresAt := timeOf (row.int 13)
    requester :=
      { ip := row.text? 14
        userAgent := row.text? 15
        approximateLocation := row.text? 16 }
    invitation := (row.text? 17).map fun value => ⟨value⟩ }

private def attemptById [Monad m] (c : Ctx m) (tenant : TenantId) (id : AttemptId tenant) :
    m (Option (AttemptState tenant)) := do
  let row ← c.first (attemptSelect ++
    sql!" WHERE tenant = {tenant.value} AND id = {id.value}")
  pure (row.map readAttempt)

private def startAttempt [Monad m] (c : Ctx m) (tenant : TenantId)
    (attempt : AttemptState tenant) : m (List (AttemptId tenant)) :=
  c.transaction fun c => do
    let identity := attempt.address.normalise
    let live ← c.rows
      sql!"SELECT id FROM {attempts}
           WHERE tenant = {tenant.value} AND identity_local = {identity.localPart}
             AND identity_domain = {domainText identity.domain}
             AND phase IN ('pending', 'revealed')"
    c.run
      sql!"UPDATE {attempts} SET phase = 'abandoned'
           WHERE tenant = {tenant.value} AND identity_local = {identity.localPart}
             AND identity_domain = {domainText identity.domain}
             AND phase IN ('pending', 'revealed')"
    c.run
      sql!"INSERT INTO {attempts}
             (tenant, id, address_local, address_domain, identity_local, identity_domain, phase,
              magic_key, magic_bytes, code_key, code_bytes, emailed_key, emailed_bytes,
              nonce_key, nonce_bytes, failed_entries, expires_at, requester_ip, requester_agent,
              requester_location, invitation_id)
           VALUES ({tenant.value}, {attempt.id.value}, {attempt.address.localPart},
             {domainText attempt.address.domain}, {identity.localPart},
             {domainText identity.domain}, {phaseText attempt.phase},
             {attempt.magicToken.keyId.value}, {digestBytesText attempt.magicToken},
             {attempt.revealedCode.keyId.value}, {digestBytesText attempt.revealedCode},
             {attempt.emailedCode.map (·.keyId.value)},
             {attempt.emailedCode.map digestBytesText},
             {attempt.bindingNonce.keyId.value}, {digestBytesText attempt.bindingNonce},
             {attempt.failedCodeEntries}, {timeText attempt.expiresAt},
             {attempt.requester.ip}, {attempt.requester.userAgent},
             {attempt.requester.approximateLocation}, {attempt.invitation.map (·.value)})"
    pure ((live.map fun r => (⟨r.text 0⟩ : AttemptId tenant)).toList)

/-- The condition names the phase and the failed-entry count the caller believed it was acting
on. Anything that changed either of them since the read wins, and this update reports that it
did not happen (AUTH-15.4.1). -/
private def commitAttempt [Monad m] (c : Ctx m) (tenant : TenantId)
    (expected next : AttemptState tenant) : m Bool := do
  let affected ← c.affected
    sql!"UPDATE {attempts}
         SET phase = {phaseText next.phase}, failed_entries = {next.failedCodeEntries}
         WHERE tenant = {tenant.value} AND id = {expected.id.value}
           AND phase = {phaseText expected.phase}
           AND failed_entries = {expected.failedCodeEntries}"
  pure (affected == 1)

/-! ## Sessions -/

private def sessionSelect : Statement :=
  sql!"SELECT id, account_id, digest_key, digest_bytes, created_at, last_seen_at,
         idle_expires_at, absolute_expires_at, user_agent, location, revoked_at
       FROM {sessions}"

private def readSession {tenant : TenantId} (row : SqlRow) : Session tenant :=
  { id := ⟨row.text 0⟩
    account := ⟨row.text 1⟩
    identifierDigest := digestOf (row.text 2) (row.text 3)
    createdAt := timeOf (row.int 4)
    lastSeenAt := timeOf (row.int 5)
    idleExpiresAt := timeOf (row.int 6)
    absoluteExpiresAt := timeOf (row.int 7)
    userAgent := row.text? 8
    approximateLocation := row.text? 9
    revokedAt := (row.int? 10).map timeOf }

private def createSession [Monad m] (c : Ctx m) (tenant : TenantId) (session : Session tenant) :
    m Unit :=
  c.run
    sql!"INSERT INTO {sessions}
           (tenant, id, account_id, digest_key, digest_bytes, created_at, last_seen_at,
            idle_expires_at, absolute_expires_at, user_agent, location, revoked_at)
         VALUES ({tenant.value}, {session.id.value}, {session.account.value},
           {session.identifierDigest.keyId.value}, {digestBytesText session.identifierDigest},
           {timeText session.createdAt}, {timeText session.lastSeenAt},
           {timeText session.idleExpiresAt}, {timeText session.absoluteExpiresAt},
           {session.userAgent}, {session.approximateLocation},
           {session.revokedAt.map timeText})"

/-- Expiry and revocation are tested in the statement, so correctness does not depend on a
sweeper having run (AUTH-15.4.3). -/
private def liveSession (now : Timestamp) : Statement :=
  sql!" AND revoked_at IS NULL AND idle_expires_at > {timeText now}
        AND absolute_expires_at > {timeText now}"

private def sessionByDigest [Monad m] (c : Ctx m) (tenant : TenantId) (now : Timestamp)
    (digest : Digest) : m (Option (Session tenant)) := do
  let row ← c.first (sessionSelect ++
    sql!" WHERE tenant = {tenant.value} AND digest_key = {digest.keyId.value}
            AND digest_bytes = {digestBytesText digest}" ++ liveSession now)
  pure (row.map readSession)

private def sessionsForAccount [Monad m] (c : Ctx m) (tenant : TenantId) (now : Timestamp)
    (account : AccountId tenant) : m (List (Session tenant)) := do
  let rows ← c.rows (sessionSelect ++
    sql!" WHERE tenant = {tenant.value} AND account_id = {account.value}" ++ liveSession now)
  pure (rows.map readSession).toList

/-- The absolute expiry is not touched, and the statement will not resurrect a session that has
already gone: a revoked or expired row is not one this can move. -/
private def touchSession [Monad m] (c : Ctx m) (tenant : TenantId) (id : SessionId tenant)
    (lastSeenAt idleExpiresAt : Timestamp) : m Unit :=
  c.run
    sql!"UPDATE {sessions}
         SET last_seen_at = {timeText lastSeenAt}, idle_expires_at = {timeText idleExpiresAt}
         WHERE tenant = {tenant.value} AND id = {id.value} AND revoked_at IS NULL
           AND idle_expires_at > {timeText lastSeenAt}
           AND absolute_expires_at > {timeText lastSeenAt}"

private def revokeSession [Monad m] (c : Ctx m) (tenant : TenantId) (now : Timestamp)
    (id : SessionId tenant) : m Unit :=
  c.run
    sql!"UPDATE {sessions} SET revoked_at = {timeText now}
         WHERE tenant = {tenant.value} AND id = {id.value} AND revoked_at IS NULL"

private def revokeSessionsForAccount [Monad m] (c : Ctx m) (tenant : TenantId) (now : Timestamp)
    (account : AccountId tenant) : m Unit :=
  c.run
    sql!"UPDATE {sessions} SET revoked_at = {timeText now}
         WHERE tenant = {tenant.value} AND account_id = {account.value} AND revoked_at IS NULL"

/-! ## Invitations -/

private def invitationSelect : Statement :=
  sql!"SELECT id, address_local, address_domain, token_key, token_bytes, metadata, state,
         expires_at, created_by, consumed_at
       FROM {invitations}"

private def readInvitation {tenant : TenantId} (row : SqlRow) : Invitation tenant :=
  { id := ⟨row.text 0⟩
    address := ⟨row.text 1, domainOfText (row.text 2)⟩
    tokenDigest := digestOf (row.text 3) (row.text 4)
    metadata := ⟨row.text 5⟩
    state := invitationStateOf (row.text 6)
    expiresAt := timeOf (row.int 7)
    createdBy := actorOf (row.text? 8)
    consumedAt := (row.int? 9).map timeOf }

private def createInvitation [Monad m] (c : Ctx m) (tenant : TenantId)
    (invitation : Invitation tenant) : m Unit :=
  c.run
    sql!"INSERT INTO {invitations}
           (tenant, id, address_local, address_domain, token_key, token_bytes, metadata, state,
            expires_at, created_by, consumed_at)
         VALUES ({tenant.value}, {invitation.id.value}, {invitation.address.localPart},
           {domainText invitation.address.domain}, {invitation.tokenDigest.keyId.value},
           {digestBytesText invitation.tokenDigest}, {invitation.metadata.payload},
           {invitationStateText invitation.state}, {timeText invitation.expiresAt},
           {actorRef invitation.createdBy}, {invitation.consumedAt.map timeText})"

private def invitationById [Monad m] (c : Ctx m) (tenant : TenantId) (id : InvitationId tenant) :
    m (Option (Invitation tenant)) := do
  let row ← c.first (invitationSelect ++
    sql!" WHERE tenant = {tenant.value} AND id = {id.value}")
  pure (row.map readInvitation)

private def commitInvitation [Monad m] (c : Ctx m) (tenant : TenantId)
    (expected next : Invitation tenant) : m Bool := do
  let affected ← c.affected
    sql!"UPDATE {invitations}
         SET state = {invitationStateText next.state},
           consumed_at = {next.consumedAt.map timeText},
           token_key = {next.tokenDigest.keyId.value},
           token_bytes = {digestBytesText next.tokenDigest},
           expires_at = {timeText next.expiresAt}
         WHERE tenant = {tenant.value} AND id = {expected.id.value}
           AND state = {invitationStateText expected.state}"
  pure (affected == 1)

private def invitationsForTenant [Monad m] (c : Ctx m) (tenant : TenantId) :
    m (List (Invitation tenant)) := do
  let rows ← c.rows (invitationSelect ++ sql!" WHERE tenant = {tenant.value}")
  pure (rows.map readInvitation).toList

/-! ## Delivery history and suppression -/

private def deliverySelect : Statement :=
  sql!"SELECT identity_local, identity_domain, suppressed_by, failures, first_failure_at,
         last_failure_at, detail
       FROM {deliveryRecords}"

private def readDelivery {tenant : TenantId} (row : SqlRow) : DeliveryRecord tenant :=
  { address := ⟨row.text 0, domainOfText (row.text 1)⟩
    suppressedBy := (row.text? 2).map suppressionOf
    failures := row.nat 3
    firstFailureAt := timeOf (row.int 4)
    lastFailureAt := timeOf (row.int 5)
    detail := row.text 6 }

private def deliveryRecord [Monad m] (c : Ctx m) (tenant : TenantId)
    (address : NormalisedEmail) : m (Option (DeliveryRecord tenant)) := do
  let row ← c.first (deliverySelect ++
    sql!" WHERE tenant = {tenant.value} AND identity_local = {address.localPart}
            AND identity_domain = {domainText address.domain}")
  pure (row.map readDelivery)

/-- Counting and suppressing in one statement, because two bounces arriving together would
otherwise be counted as one, and the count is what the report of AUTH-12.5 is made of. A
suppression already in force is kept: `COALESCE` takes the stored reason when the new failure
supplies none, which is what makes a later soft bounce unable to lift a hard one. -/
private def recordDeliveryFailure [Monad m] (c : Ctx m) (tenant : TenantId)
    (address : NormalisedEmail) (failure : DeliveryFailure) (now : Timestamp) (detail : String) :
    m (DeliveryRecord tenant) :=
  c.transaction fun c => do
    let reason := failure.suppression.map suppressionText
    c.run
      sql!"INSERT INTO {deliveryRecords}
             (tenant, identity_local, identity_domain, suppressed_by, failures,
              first_failure_at, last_failure_at, detail)
           VALUES ({tenant.value}, {address.localPart}, {domainText address.domain}, {reason},
             1, {timeText now}, {timeText now}, {detail})
           ON CONFLICT (tenant, identity_local, identity_domain) DO UPDATE
             SET suppressed_by =
                   COALESCE(EXCLUDED.suppressed_by, {deliveryRecords}.suppressed_by),
               failures = {deliveryRecords}.failures + 1,
               last_failure_at = {timeText now},
               detail = {detail}"
    let stored ← deliveryRecord c tenant address
    pure (stored.getD (DeliveryRecord.first address failure now detail))

private def suppressAddress [Monad m] (c : Ctx m) (tenant : TenantId) (address : NormalisedEmail)
    (now : Timestamp) (detail : String) : m (DeliveryRecord tenant) :=
  c.transaction fun c => do
    c.run
      sql!"INSERT INTO {deliveryRecords}
             (tenant, identity_local, identity_domain, suppressed_by, failures,
              first_failure_at, last_failure_at, detail)
           VALUES ({tenant.value}, {address.localPart}, {domainText address.domain}, 'client',
             0, {timeText now}, {timeText now}, {detail})
           ON CONFLICT (tenant, identity_local, identity_domain) DO UPDATE
             SET suppressed_by = 'client', last_failure_at = {timeText now}, detail = {detail}"
    let stored ← deliveryRecord c tenant address
    pure (stored.getD
      { address, suppressedBy := some .client, failures := 0, firstFailureAt := now,
        lastFailureAt := now, detail })

private def allDeliveryRecords [Monad m] (c : Ctx m) (tenant : TenantId) :
    m (List (DeliveryRecord tenant)) := do
  let rows ← c.rows (deliverySelect ++ sql!" WHERE tenant = {tenant.value}")
  pure (rows.map readDelivery).toList

private def clearSuppression [Monad m] (c : Ctx m) (tenant : TenantId)
    (address : NormalisedEmail) : m Unit :=
  c.run
    sql!"DELETE FROM {deliveryRecords}
         WHERE tenant = {tenant.value} AND identity_local = {address.localPart}
           AND identity_domain = {domainText address.domain}"

/-! ## Consent

Insert and select, and nothing else. There is no update and no delete because AUTH-4.6.3 admits
neither, and a table with no statement that rewrites a row cannot have one written by accident.
-/

private def recordConsent [Monad m] (c : Ctx m) (tenant : TenantId)
    (entry : ConsentEntry tenant) : m Unit :=
  c.run
    sql!"INSERT INTO {consents} (tenant, account, subject, version, act, recorded_at)
         VALUES ({tenant.value}, {entry.account.value}, {entry.subject.name}, {entry.version},
           {consentActText entry.act}, {timeText entry.recordedAt})"

private def consentHistory [Monad m] (c : Ctx m) (tenant : TenantId)
    (account : AccountId tenant) : m (List (ConsentEntry tenant)) := do
  let rows ← c.rows
    sql!"SELECT subject, version, act, recorded_at
         FROM {consents} WHERE tenant = {tenant.value} AND account = {account.value}
         ORDER BY seq"
  pure (rows.map fun row =>
    { account
      subject := ⟨row.text 0⟩
      version := row.text 1
      act := consentActOf (row.text 2)
      recordedAt := timeOf (row.int 3) }).toList

/-- The last word on the subject, per account, and only where it was a grant. `seq` decides
which entry is last rather than the timestamp, because two entries can share a second and the
one that arrived second is the one that counts. -/
private def consentingAccounts [Monad m] (c : Ctx m) (tenant : TenantId)
    (subject : ConsentSubject) : m (List (AccountId tenant)) := do
  let rows ← c.rows
    sql!"SELECT account FROM {consents} said
         WHERE said.tenant = {tenant.value} AND said.subject = {subject.name}
           AND said.act = 'granted'
           AND said.seq = (SELECT MAX(latest.seq) FROM {consents} latest
                           WHERE latest.tenant = said.tenant AND latest.account = said.account
                             AND latest.subject = said.subject)
         ORDER BY said.account"
  pure (rows.map fun row => ⟨row.text 0⟩).toList

/-! ## Audit -/

private def appendAudit [Monad m] (c : Ctx m) (tenant : TenantId) (entry : AuditEntry tenant) :
    m Unit :=
  let (kind, subject, detail) := auditColumns entry.event
  c.run
    sql!"INSERT INTO {audit} (tenant, occurred_at, actor_ref, kind, subject, detail)
         VALUES ({tenant.value}, {timeText entry.occurredAt}, {actorRef entry.actor}, {kind},
           {subject}, {detail})"

private def auditEntries [Monad m] (c : Ctx m) (tenant : TenantId) :
    m (List (AuditEntry tenant)) := do
  let rows ← c.rows
    sql!"SELECT occurred_at, actor_ref, kind, subject, detail
         FROM {audit} WHERE tenant = {tenant.value} ORDER BY seq"
  pure (rows.toList.filterMap fun row =>
    (auditEventOf tenant (row.text 2) (row.text 3) (row.text 4)).map fun event =>
      { occurredAt := timeOf (row.int 0), actor := actorOf (row.text? 1), event })

/-! ## Sweeping -/

/-- A session is removed once nothing can reach it: past its absolute lifetime, past the idle
timeout it was last written with, or revoked. Those are the three `Session.identify` refuses on,
and `touchSession` cannot resurrect one, so a row matching any of them is unreachable rather than
merely stale. -/
private def purgeExpired [Monad m] (c : Ctx m) (tenant : TenantId) (before : Timestamp) :
    m PurgeCounts :=
  c.transaction fun c => do
    let attemptsRemoved ← c.affected
      sql!"DELETE FROM {attempts}
           WHERE tenant = {tenant.value} AND expires_at < {timeText before}"
    let sessionsRemoved ← c.affected
      sql!"DELETE FROM {sessions}
           WHERE tenant = {tenant.value}
             AND (absolute_expires_at < {timeText before}
                  OR idle_expires_at < {timeText before}
                  OR revoked_at < {timeText before})"
    pure { attempts := attemptsRemoved, sessions := sessionsRemoved }

private def deleteTenant [Monad m] (c : Ctx m) (tenant : TenantId) : m Unit :=
  c.transaction fun c => do
    c.run sql!"DELETE FROM {accountEmails} WHERE tenant = {tenant.value}"
    c.run sql!"DELETE FROM {accounts} WHERE tenant = {tenant.value}"
    c.run sql!"DELETE FROM {attempts} WHERE tenant = {tenant.value}"
    c.run sql!"DELETE FROM {sessions} WHERE tenant = {tenant.value}"
    c.run sql!"DELETE FROM {invitations} WHERE tenant = {tenant.value}"
    c.run sql!"DELETE FROM {deliveryRecords} WHERE tenant = {tenant.value}"
    c.run sql!"DELETE FROM {consents} WHERE tenant = {tenant.value}"
    c.run sql!"DELETE FROM {audit} WHERE tenant = {tenant.value}"

/-- The port, for any dialect and any driver that can bind parameters and report rows affected
(AUTH-15.2.2). -/
def sqlAuthStore [Monad m] (dialect : Dialect) (conn : SqlConnection m) : AuthStore m :=
  let c : Ctx m := { dialect, conn }
  { accountByIdentity := accountByIdentity c
    createAccount := createAccount c
    accountById := accountById c
    setPrimaryEmail := setPrimaryEmail c
    setAccountStatus := setAccountStatus c
    startAttempt := startAttempt c
    attemptById := attemptById c
    commitAttempt := commitAttempt c
    createSession := createSession c
    sessionByDigest := sessionByDigest c
    sessionsForAccount := sessionsForAccount c
    touchSession := touchSession c
    revokeSession := revokeSession c
    revokeSessionsForAccount := revokeSessionsForAccount c
    createInvitation := createInvitation c
    invitationById := invitationById c
    commitInvitation := commitInvitation c
    invitationsForTenant := invitationsForTenant c
    recordDeliveryFailure := recordDeliveryFailure c
    suppressAddress := suppressAddress c
    deliveryRecord := deliveryRecord c
    deliveryRecords := allDeliveryRecords c
    clearSuppression := clearSuppression c
    recordConsent := recordConsent c
    consentHistory := consentHistory c
    consentingAccounts := consentingAccounts c
    appendAudit := appendAudit c
    auditEntries := auditEntries c
    purgeExpired := purgeExpired c
    deleteTenant := deleteTenant c }

/-- The transactional capability (AUTH-15.3), for a driver whose `transaction` nests or whose
backend does not need it to. The block runs against the same connection, which is the price
AUTH-15.3.5 requires be stated: the library's tables live in the client's own database. -/
def sqlTransactionalStore [Monad m] (dialect : Dialect) (conn : SqlConnection m) :
    TransactionalStore m :=
  { store := sqlAuthStore dialect conn
    runInTx := fun action => conn.transaction fun conn => action (sqlAuthStore dialect conn) }

end Authentication.Sql
