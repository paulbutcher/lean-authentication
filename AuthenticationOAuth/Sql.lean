/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import AuthenticationOAuth.Store
public import AuthenticationSql

/-!
One implementation of `OAuthStore` for every SQL backend (AUTH-20.15.3).

The same arrangement the core store uses, and for the same reason: the two compare-and-set
statements are where a bug is a vulnerability, and two independent implementations would be two
independent chances to write one wrong. What a backend still owns is its schema, its dialect and
its driver adapter.

The schema is separate from the core library's rather than folded into it, so that a deployment
taking only the sign-in flow creates none of these tables. It ships as migrations beside the
others and is embedded here for the same reason they are embedded there: one copy of it rather
than two that can drift.
-/

public section

namespace Authentication.OAuth

open Authentication.Sql

/-! ## Schema -/

def sqliteSchemaSql : String :=
  include_str "../migrations/sqlite/20260824120000_authentication_oauth.up.sql"

def postgresSchemaSql : String :=
  include_str "../migrations/postgres/20260824120000_authentication_oauth.up.sql"

private def clients : TableName := ⟨"oauth_clients"⟩
private def documents : TableName := ⟨"oauth_documents"⟩
private def codes : TableName := ⟨"oauth_codes"⟩
private def accessTokens : TableName := ⟨"oauth_access_tokens"⟩
private def refreshTokens : TableName := ⟨"oauth_refresh_tokens"⟩

/-- The tables these statements read and write, as the bare names `Dialect.table` qualifies. -/
def oauthTableNames : List String :=
  [clients.value, documents.value, codes.value, accessTokens.value, refreshTokens.value]

/-! ## Encoding between domain values and columns -/

private def digestBytesText (d : Digest) : String := Codec.Base64Url.encodeString d.bytes

private def digestOf (keyId bytes : String) : Digest :=
  ⟨⟨keyId⟩, (Codec.Base64Url.decodeString bytes).getD ⟨#[]⟩⟩

private def timeText (t : Timestamp) : Int := t.epochSeconds

/-- The metadata is held as the JSON this library would have emitted for it, in one column, so
that a field arriving in a later revision of RFC 7591 is a change to one reader rather than to
five backends' schemas. -/
private def metadataText (id : ClientId) (metadata : ClientMetadata) : String :=
  (ClientMetadata.toJson id metadata).compress

private def metadataOf (text : String) : Option ClientMetadata :=
  match Json.parse text with
  | .error _ => none
  | .ok document => (ClientMetadata.ofJson document false).toOption

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

private def Ctx.transaction [Monad m] {α : Type} (c : Ctx m) (action : Ctx m → m α) : m α :=
  c.conn.transaction fun conn => action { c with conn }

/-! ## Clients -/

private def readClient {tenant : TenantId} (row : SqlRow) : Option (ClientRecord tenant) :=
  (metadataOf (row.text 1)).map fun metadata =>
    { id := ⟨row.text 0⟩
      metadata
      registeredAt := ⟨row.int 2⟩
      lastUsedAt := ⟨row.int 3⟩ }

private def clientSelect : Statement :=
  sql!"SELECT id, metadata, registered_at, last_used_at FROM {clients}"

private def createClient [Monad m] (c : Ctx m) (tenant : TenantId)
    (record : ClientRecord tenant) : m Unit :=
  c.run
    sql!"INSERT INTO {clients} (tenant, id, metadata, registered_at, last_used_at)
         VALUES ({tenant.value}, {record.id.value},
           {metadataText record.id record.metadata}, {timeText record.registeredAt},
           {timeText record.lastUsedAt})
         ON CONFLICT DO NOTHING"

private def clientById [Monad m] (c : Ctx m) (tenant : TenantId) (id : ClientId) :
    m (Option (ClientRecord tenant)) := do
  let row ← c.first (clientSelect ++ sql!" WHERE tenant = {tenant.value} AND id = {id.value}")
  pure (row.bind readClient)

private def allClients [Monad m] (c : Ctx m) (tenant : TenantId) :
    m (List (ClientRecord tenant)) := do
  let rows ← c.rows (clientSelect ++ sql!" WHERE tenant = {tenant.value} ORDER BY registered_at")
  pure (rows.toList.filterMap readClient)

private def touchClient [Monad m] (c : Ctx m) (tenant : TenantId) (id : ClientId)
    (now : Timestamp) : m Unit :=
  c.run
    sql!"UPDATE {clients} SET last_used_at = {timeText now}
         WHERE tenant = {tenant.value} AND id = {id.value}"

/-- Removes the client and everything issued to it. The consent records naming it are left
where they are: they are evidence of what somebody agreed to, and an accumulated registration
going away does not make that untrue. -/
private def forgetClient [Monad m] (c : Ctx m) (tenant : TenantId) (id : String) : m Unit := do
  c.run sql!"DELETE FROM {codes} WHERE tenant = {tenant.value} AND client_id = {id}"
  c.run sql!"DELETE FROM {accessTokens} WHERE tenant = {tenant.value} AND client_id = {id}"
  c.run sql!"DELETE FROM {refreshTokens} WHERE tenant = {tenant.value} AND client_id = {id}"
  c.run sql!"DELETE FROM {documents} WHERE tenant = {tenant.value} AND client_id = {id}"

private def deleteClient [Monad m] (c : Ctx m) (tenant : TenantId) (id : ClientId) : m Unit :=
  c.transaction fun c => do
    forgetClient c tenant id.value
    c.run sql!"DELETE FROM {clients} WHERE tenant = {tenant.value} AND id = {id.value}"

private def pruneClients [Monad m] (c : Ctx m) (tenant : TenantId) (unusedSince : Timestamp) :
    m Nat :=
  c.transaction fun c => do
    let doomed ← c.rows
      sql!"SELECT id FROM {clients}
           WHERE tenant = {tenant.value} AND last_used_at < {timeText unusedSince}"
    for row in doomed do
      forgetClient c tenant (row.text 0)
    c.affected
      sql!"DELETE FROM {clients}
           WHERE tenant = {tenant.value} AND last_used_at < {timeText unusedSince}"

/-! ## Metadata documents -/

/-- Replaces whatever was there, in one transaction rather than through a dialect's upsert
syntax: `ON CONFLICT DO NOTHING` is spelled the same in both backends and `DO UPDATE` is one
more thing that would have to be. -/
private def cacheDocument [Monad m] (c : Ctx m) (tenant : TenantId)
    (cached : CachedDocument tenant) : m Unit :=
  c.transaction fun c => do
    c.run
      sql!"DELETE FROM {documents}
           WHERE tenant = {tenant.value} AND client_id = {cached.client.value}"
    c.run
      sql!"INSERT INTO {documents} (tenant, client_id, metadata, fetched_at, fresh_until)
           VALUES ({tenant.value}, {cached.client.value},
             {metadataText cached.client cached.metadata}, {timeText cached.fetchedAt},
             {timeText cached.freshUntil})"

/-- Freshness is tested in the statement, so a stale document is not something a caller can
forget to check. -/
private def cachedDocument [Monad m] (c : Ctx m) (tenant : TenantId) (id : ClientId)
    (now : Timestamp) : m (Option (CachedDocument tenant)) := do
  let row ← c.first
    sql!"SELECT metadata, fetched_at, fresh_until FROM {documents}
         WHERE tenant = {tenant.value} AND client_id = {id.value}
           AND fresh_until > {timeText now}"
  pure <| row.bind fun row =>
    (metadataOf (row.text 0)).map fun metadata =>
      { client := id, metadata, fetchedAt := ⟨row.int 1⟩, freshUntil := ⟨row.int 2⟩ }

private def forgetDocument [Monad m] (c : Ctx m) (tenant : TenantId) (id : ClientId) : m Unit :=
  c.run sql!"DELETE FROM {documents} WHERE tenant = {tenant.value} AND client_id = {id.value}"

/-! ## Authorization codes -/

private def codeSelect : Statement :=
  sql!"SELECT grant_id, digest_key, digest_bytes, account_id, client_id, redirect_uri,
         redirect_uri_given, code_challenge, resource, scopes, issued_at, expires_at, redeemed_at
       FROM {codes}"

private def readCode {tenant : TenantId} (row : SqlRow) : AuthorizationCode tenant :=
  { grant := ⟨row.text 0⟩
    digest := digestOf (row.text 1) (row.text 2)
    account := ⟨row.text 3⟩
    client := ⟨row.text 4⟩
    redirectUri := row.text 5
    redirectUriGiven := row.int 6 != 0
    codeChallenge := row.text 7
    resource := ⟨row.text 8⟩
    scopes := Scope.parse (row.text 9)
    issuedAt := ⟨row.int 10⟩
    expiresAt := ⟨row.int 11⟩
    redeemedAt := (row.int? 12).map fun value => ⟨value⟩ }

private def createCode [Monad m] (c : Ctx m) (tenant : TenantId)
    (code : AuthorizationCode tenant) : m Unit :=
  c.run
    sql!"INSERT INTO {codes}
           (tenant, digest_key, digest_bytes, grant_id, account_id, client_id, redirect_uri,
            redirect_uri_given, code_challenge, resource, scopes, issued_at, expires_at,
            redeemed_at)
         VALUES ({tenant.value}, {code.digest.keyId.value}, {digestBytesText code.digest},
           {code.grant.value}, {code.account.value}, {code.client.value}, {code.redirectUri},
           {code.redirectUriGiven}, {code.codeChallenge}, {code.resource.value},
           {Scope.render code.scopes}, {timeText code.issuedAt}, {timeText code.expiresAt},
           {code.redeemedAt.map timeText})"

private def codeByDigest [Monad m] (c : Ctx m) (tenant : TenantId) (digest : Digest) :
    m (Option (AuthorizationCode tenant)) := do
  let row ← c.first (codeSelect ++
    sql!" WHERE tenant = {tenant.value} AND digest_key = {digest.keyId.value}
            AND digest_bytes = {digestBytesText digest}")
  pure (row.map readCode)

/-- The condition names the redemption the caller believed it was acting on. Anything that
redeemed the code since the read wins, and this reports that it did not happen. -/
private def commitCode [Monad m] (c : Ctx m) (tenant : TenantId)
    (expected next : AuthorizationCode tenant) : m Bool := do
  let unchanged := match expected.redeemedAt with
    | none => sql!" AND redeemed_at IS NULL"
    | some stamp => sql!" AND redeemed_at = {timeText stamp}"
  let affected ← c.affected
    (sql!"UPDATE {codes} SET redeemed_at = {next.redeemedAt.map timeText}
          WHERE tenant = {tenant.value} AND digest_key = {expected.digest.keyId.value}
            AND digest_bytes = {digestBytesText expected.digest}" ++ unchanged)
  pure (affected == 1)

/-! ## Tokens -/

private def accessSelect : Statement :=
  sql!"SELECT grant_id, digest_key, digest_bytes, account_id, client_id, resource, scopes,
         issued_at, expires_at, revoked_at
       FROM {accessTokens}"

private def readAccessToken {tenant : TenantId} (row : SqlRow) : AccessToken tenant :=
  { grant := ⟨row.text 0⟩
    digest := digestOf (row.text 1) (row.text 2)
    account := ⟨row.text 3⟩
    client := ⟨row.text 4⟩
    resource := ⟨row.text 5⟩
    scopes := Scope.parse (row.text 6)
    issuedAt := ⟨row.int 7⟩
    expiresAt := ⟨row.int 8⟩
    revokedAt := (row.int? 9).map fun value => ⟨value⟩ }

private def createAccessToken [Monad m] (c : Ctx m) (tenant : TenantId)
    (token : AccessToken tenant) : m Unit :=
  c.run
    sql!"INSERT INTO {accessTokens}
           (tenant, digest_key, digest_bytes, grant_id, account_id, client_id, resource, scopes,
            issued_at, expires_at, revoked_at)
         VALUES ({tenant.value}, {token.digest.keyId.value}, {digestBytesText token.digest},
           {token.grant.value}, {token.account.value}, {token.client.value},
           {token.resource.value}, {Scope.render token.scopes}, {timeText token.issuedAt},
           {timeText token.expiresAt}, {token.revokedAt.map timeText})"

private def accessTokenByDigest [Monad m] (c : Ctx m) (tenant : TenantId) (digest : Digest) :
    m (Option (AccessToken tenant)) := do
  let row ← c.first (accessSelect ++
    sql!" WHERE tenant = {tenant.value} AND digest_key = {digest.keyId.value}
            AND digest_bytes = {digestBytesText digest}")
  pure (row.map readAccessToken)

private def refreshSelect : Statement :=
  sql!"SELECT grant_id, digest_key, digest_bytes, account_id, client_id, resource, scopes,
         issued_at, expires_at, replaced_at, revoked_at
       FROM {refreshTokens}"

private def readRefreshToken {tenant : TenantId} (row : SqlRow) : RefreshToken tenant :=
  { grant := ⟨row.text 0⟩
    digest := digestOf (row.text 1) (row.text 2)
    account := ⟨row.text 3⟩
    client := ⟨row.text 4⟩
    resource := ⟨row.text 5⟩
    scopes := Scope.parse (row.text 6)
    issuedAt := ⟨row.int 7⟩
    expiresAt := ⟨row.int 8⟩
    replacedAt := (row.int? 9).map fun value => ⟨value⟩
    revokedAt := (row.int? 10).map fun value => ⟨value⟩ }

private def createRefreshToken [Monad m] (c : Ctx m) (tenant : TenantId)
    (token : RefreshToken tenant) : m Unit :=
  c.run
    sql!"INSERT INTO {refreshTokens}
           (tenant, digest_key, digest_bytes, grant_id, account_id, client_id, resource, scopes,
            issued_at, expires_at, replaced_at, revoked_at)
         VALUES ({tenant.value}, {token.digest.keyId.value}, {digestBytesText token.digest},
           {token.grant.value}, {token.account.value}, {token.client.value},
           {token.resource.value}, {Scope.render token.scopes}, {timeText token.issuedAt},
           {timeText token.expiresAt}, {token.replacedAt.map timeText},
           {token.revokedAt.map timeText})"

private def refreshTokenByDigest [Monad m] (c : Ctx m) (tenant : TenantId) (digest : Digest) :
    m (Option (RefreshToken tenant)) := do
  let row ← c.first (refreshSelect ++
    sql!" WHERE tenant = {tenant.value} AND digest_key = {digest.keyId.value}
            AND digest_bytes = {digestBytesText digest}")
  pure (row.map readRefreshToken)

/-- Rotation under compare and set, so two requests presenting one refresh token produce one new
token and one revoked grant. -/
private def commitRefreshToken [Monad m] (c : Ctx m) (tenant : TenantId)
    (expected next : RefreshToken tenant) : m Bool := do
  let unchanged := match expected.replacedAt with
    | none => sql!" AND replaced_at IS NULL"
    | some stamp => sql!" AND replaced_at = {timeText stamp}"
  let affected ← c.affected
    (sql!"UPDATE {refreshTokens}
          SET replaced_at = {next.replacedAt.map timeText},
            revoked_at = {next.revokedAt.map timeText}
          WHERE tenant = {tenant.value} AND digest_key = {expected.digest.keyId.value}
            AND digest_bytes = {digestBytesText expected.digest}" ++ unchanged)
  pure (affected == 1)

/-! ## What an account holds -/

private def readLiveGrant {tenant : TenantId} (row : SqlRow) : GrantSummary tenant :=
  { client := ⟨row.text 0⟩
    resource := ⟨row.text 1⟩
    scopes := Scope.parse (row.text 2)
    lastIssuedAt := ⟨row.int 3⟩ }

/-- Collapses the credentials under one grant into the row a listing shows. Two of them differ
in their scopes only where a refresh narrowed them, and then the newest is the one that says
what can be done now. -/
private def mergeLiveGrant {tenant : TenantId} (summaries : List (GrantSummary tenant))
    (found : GrantSummary tenant) : List (GrantSummary tenant) :=
  let sameGrant := fun (s : GrantSummary tenant) =>
    s.client == found.client && s.resource == found.resource
  if summaries.any sameGrant then
    summaries.map fun s =>
      if sameGrant s && decide (s.lastIssuedAt ≤ found.lastIssuedAt) then found else s
  else summaries ++ [found]

/--
The credentials that still permit something, from both tables at once.

A refresh token that has been rotated is excluded as well as one that has been revoked: it
cannot be exchanged again, and the token that replaced it is a row of its own. Combining the
two tables in the statement rather than in two round trips is what lets the account and client
index carry the whole query.
-/
private def grantsForAccount [Monad m] (c : Ctx m) (tenant : TenantId)
    (account : AccountId tenant) (now : Timestamp) : m (List (GrantSummary tenant)) := do
  let rows ← c.rows
    sql!"SELECT client_id, resource, scopes, issued_at FROM {accessTokens}
         WHERE tenant = {tenant.value} AND account_id = {account.value}
           AND revoked_at IS NULL AND expires_at > {timeText now}
         UNION ALL
         SELECT client_id, resource, scopes, issued_at FROM {refreshTokens}
         WHERE tenant = {tenant.value} AND account_id = {account.value}
           AND revoked_at IS NULL AND replaced_at IS NULL AND expires_at > {timeText now}
         ORDER BY issued_at"
  pure ((rows.toList.map readLiveGrant).foldl mergeLiveGrant [])

/-! ## Revocation and sweeping -/

private def revokeGrant [Monad m] (c : Ctx m) (tenant : TenantId) (now : Timestamp)
    (grant : GrantId tenant) : m Unit :=
  c.transaction fun c => do
    c.run
      sql!"UPDATE {accessTokens} SET revoked_at = {timeText now}
           WHERE tenant = {tenant.value} AND grant_id = {grant.value} AND revoked_at IS NULL"
    c.run
      sql!"UPDATE {refreshTokens} SET revoked_at = {timeText now}
           WHERE tenant = {tenant.value} AND grant_id = {grant.value} AND revoked_at IS NULL"
    c.run
      sql!"UPDATE {codes} SET redeemed_at = {timeText now}
           WHERE tenant = {tenant.value} AND grant_id = {grant.value} AND redeemed_at IS NULL"

private def revokeGrants [Monad m] (c : Ctx m) (tenant : TenantId) (now : Timestamp)
    (account : AccountId tenant) (client : ClientId) (resource : ResourceIndicator) : m Unit :=
  c.transaction fun c => do
    c.run
      sql!"UPDATE {accessTokens} SET revoked_at = {timeText now}
           WHERE tenant = {tenant.value} AND account_id = {account.value}
             AND client_id = {client.value} AND resource = {resource.value}
             AND revoked_at IS NULL"
    c.run
      sql!"UPDATE {refreshTokens} SET revoked_at = {timeText now}
           WHERE tenant = {tenant.value} AND account_id = {account.value}
             AND client_id = {client.value} AND resource = {resource.value}
             AND revoked_at IS NULL"
    c.run
      sql!"UPDATE {codes} SET redeemed_at = {timeText now}
           WHERE tenant = {tenant.value} AND account_id = {account.value}
             AND client_id = {client.value} AND resource = {resource.value}
             AND redeemed_at IS NULL"

/--
A redeemed code and a rotated refresh token are kept until they expire, and deliberately: the
record of a spent credential is the only thing that can tell a replay from an unknown token, and
removing it early turns the second presentation of a stolen refresh token into a shrug rather
than a revocation.
-/
private def purgeExpired [Monad m] (c : Ctx m) (tenant : TenantId) (before : Timestamp) :
    m SweepCounts :=
  c.transaction fun c => do
    let codesRemoved ← c.affected
      sql!"DELETE FROM {codes}
           WHERE tenant = {tenant.value} AND expires_at < {timeText before}"
    let accessRemoved ← c.affected
      sql!"DELETE FROM {accessTokens}
           WHERE tenant = {tenant.value}
             AND (expires_at < {timeText before} OR revoked_at < {timeText before})"
    let refreshRemoved ← c.affected
      sql!"DELETE FROM {refreshTokens}
           WHERE tenant = {tenant.value}
             AND (expires_at < {timeText before} OR revoked_at < {timeText before})"
    let documentsRemoved ← c.affected
      sql!"DELETE FROM {documents}
           WHERE tenant = {tenant.value} AND fresh_until < {timeText before}"
    pure
      { codes := codesRemoved
        accessTokens := accessRemoved
        refreshTokens := refreshRemoved
        documents := documentsRemoved }

private def deleteTenant [Monad m] (c : Ctx m) (tenant : TenantId) : m Unit :=
  c.transaction fun c => do
    c.run sql!"DELETE FROM {codes} WHERE tenant = {tenant.value}"
    c.run sql!"DELETE FROM {accessTokens} WHERE tenant = {tenant.value}"
    c.run sql!"DELETE FROM {refreshTokens} WHERE tenant = {tenant.value}"
    c.run sql!"DELETE FROM {documents} WHERE tenant = {tenant.value}"
    c.run sql!"DELETE FROM {clients} WHERE tenant = {tenant.value}"

/-- The port, for any dialect and any driver that can bind parameters and report rows affected.
The dialect is the backend's own, so a deployment already holding one for the core store passes
the same value here. -/
def sqlOAuthStore [Monad m] (dialect : Dialect) (conn : SqlConnection m) : OAuthStore m :=
  let c : Ctx m := { dialect, conn }
  { createClient := createClient c
    clientById := clientById c
    clients := allClients c
    touchClient := touchClient c
    pruneClients := pruneClients c
    deleteClient := deleteClient c
    cacheDocument := cacheDocument c
    cachedDocument := cachedDocument c
    forgetDocument := forgetDocument c
    createCode := createCode c
    codeByDigest := codeByDigest c
    commitCode := commitCode c
    createAccessToken := createAccessToken c
    accessTokenByDigest := accessTokenByDigest c
    createRefreshToken := createRefreshToken c
    refreshTokenByDigest := refreshTokenByDigest c
    commitRefreshToken := commitRefreshToken c
    revokeGrant := revokeGrant c
    revokeGrants := revokeGrants c
    grantsForAccount := grantsForAccount c
    purgeExpired := purgeExpired c
    deleteTenant := deleteTenant c }

end Authentication.OAuth
