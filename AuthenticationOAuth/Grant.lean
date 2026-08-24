/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Authentication.Account
public import AuthenticationOAuth.Client
public import AuthenticationOAuth.Pkce
public import AuthenticationOAuth.Scope

/-!
Codes and tokens as pure state (§20.10).

Nothing here performs an effect. A code decides on its own whether it may be spent, and the
store's compare-and-set is conditioned on the stamp that decision writes, so "a code is
redeemed at most once" is a property of this file rather than a rule each backend is asked to
follow.

Every access token this library issues is built from an `Entitlement`, and an entitlement comes
either from redeeming a code or from rotating a refresh token. That is what makes the audience
and the scopes of a token facts about the request that asked for it.
-/

@[expose] public section

namespace Authentication.OAuth

/-- One decision by one person about one client and one resource. Everything issued under it
shares it, so revoking is one operation rather than a search. -/
structure GrantId (tenant : TenantId) where
  value : String
  deriving DecidableEq, Repr

/-- Why a code or a token was refused. All of them reach the client as `invalid_grant`; the
distinction is for the operator, who is the one who has to tell a wrong verifier from a
replayed code. -/
inductive GrantRejection where
  | unknown
  | expired
  | alreadyRedeemed
  | revoked
  | clientMismatch
  | redirectMismatch
  | resourceMismatch
  | verifierMismatch
  | scopeExceeded
  deriving DecidableEq, Repr, Inhabited

/-- Bound to its client, its redirect URI, its challenge, its resource and the scopes that were
consented to, and to nothing the token request gets to choose. -/
structure AuthorizationCode (tenant : TenantId) where
  grant : GrantId tenant
  digest : Digest
  account : AccountId tenant
  client : ClientId
  redirectUri : String
  /-- Whether the authorization request named it. OAuth 2.1 §4.1.3 requires the token request to
  repeat it exactly when it did, and permits its absence when it did not. -/
  redirectUriGiven : Bool
  codeChallenge : String
  resource : ResourceIndicator
  scopes : List Scope
  issuedAt : Timestamp
  expiresAt : Timestamp
  redeemedAt : Option Timestamp := none
  deriving DecidableEq, Repr

/-- What redeeming a code, or rotating a refresh token, entitles the client to. -/
structure Entitlement (tenant : TenantId) where
  grant : GrantId tenant
  account : AccountId tenant
  client : ClientId
  /-- The audience of every token built from this. -/
  resource : ResourceIndicator
  scopes : List Scope
  deriving DecidableEq, Repr

structure AccessToken (tenant : TenantId) where
  grant : GrantId tenant
  digest : Digest
  account : AccountId tenant
  client : ClientId
  /-- The `resource` the request that produced this token named. A resource server that is not
  this rejects it. -/
  resource : ResourceIndicator
  scopes : List Scope
  issuedAt : Timestamp
  expiresAt : Timestamp
  revokedAt : Option Timestamp := none
  deriving DecidableEq, Repr

structure RefreshToken (tenant : TenantId) where
  grant : GrantId tenant
  digest : Digest
  account : AccountId tenant
  client : ClientId
  resource : ResourceIndicator
  scopes : List Scope
  issuedAt : Timestamp
  expiresAt : Timestamp
  /-- Rotation, which OAuth 2.1 §4.3.1 requires for a public client and every client here is.
  A token that has been exchanged is dead, and presenting it again is not merely refused: it is
  evidence that one of the two holders is not the client, so the whole grant goes. -/
  replacedAt : Option Timestamp := none
  revokedAt : Option Timestamp := none
  deriving DecidableEq, Repr

namespace AuthorizationCode

/-- Single use and short lived. The stamp this writes is what the store's compare-and-set is
conditioned on, so the second of two concurrent redemptions writes nothing and is told so. -/
def redeem (now : Timestamp) {tenant : TenantId} (code : AuthorizationCode tenant) :
    Except GrantRejection (AuthorizationCode tenant) :=
  if code.redeemedAt.isSome then .error .alreadyRedeemed
  else if code.expiresAt ≤ now then .error .expired
  else .ok { code with redeemedAt := some now }

/--
Everything the code is bound to, checked before it is spent.

The redirect URI is compared exactly and not with the loopback rule of `Uri.admits`: what is
being compared here is against the URI the authorization request already matched, so a
difference is a different request rather than a different port.
-/
def bindings {tenant : TenantId} (code : AuthorizationCode tenant) (client : ClientId)
    (redirectUri : Option String) (verifier : String) (resource : ResourceIndicator) :
    Except GrantRejection Unit :=
  if code.client != client then .error .clientMismatch
  else
    match redirectUri with
    | some presented => if presented != code.redirectUri then .error .redirectMismatch else rest
    | none => if code.redirectUriGiven then .error .redirectMismatch else rest
where
  rest : Except GrantRejection Unit :=
    if code.resource != resource then .error .resourceMismatch
    else if !Pkce.verify code.codeChallenge verifier then .error .verifierMismatch
    else .ok ()

def entitlement {tenant : TenantId} (code : AuthorizationCode tenant) : Entitlement tenant :=
  { grant := code.grant
    account := code.account
    client := code.client
    resource := code.resource
    scopes := code.scopes }

end AuthorizationCode

/-- What an authorization request has settled by the time a code exists. The scopes are decided
here rather than at the token endpoint, so the token endpoint has nothing left to choose. -/
structure GrantDecision (tenant : TenantId) where
  grant : GrantId tenant
  account : AccountId tenant
  client : ClientId
  redirectUri : String
  redirectUriGiven : Bool
  codeChallenge : String
  resource : ResourceIndicator
  requestedScopes : List Scope
  consentedScopes : List Scope
  deriving DecidableEq, Repr

def GrantDecision.code {tenant : TenantId} (decision : GrantDecision tenant) (digest : Digest)
    (now : Timestamp) (lifetime : Duration) : AuthorizationCode tenant :=
  { grant := decision.grant
    digest
    account := decision.account
    client := decision.client
    redirectUri := decision.redirectUri
    redirectUriGiven := decision.redirectUriGiven
    codeChallenge := decision.codeChallenge
    resource := decision.resource
    scopes := Scope.granted decision.requestedScopes decision.consentedScopes
    issuedAt := now
    expiresAt := now.advance lifetime }

namespace Entitlement

def accessToken {tenant : TenantId} (entitlement : Entitlement tenant) (digest : Digest)
    (now : Timestamp) (lifetime : Duration) : AccessToken tenant :=
  { grant := entitlement.grant
    digest
    account := entitlement.account
    client := entitlement.client
    resource := entitlement.resource
    scopes := entitlement.scopes
    issuedAt := now
    expiresAt := now.advance lifetime }

def refreshToken {tenant : TenantId} (entitlement : Entitlement tenant) (digest : Digest)
    (now : Timestamp) (lifetime : Duration) : RefreshToken tenant :=
  { grant := entitlement.grant
    digest
    account := entitlement.account
    client := entitlement.client
    resource := entitlement.resource
    scopes := entitlement.scopes
    issuedAt := now
    expiresAt := now.advance lifetime }

end Entitlement

namespace RefreshToken

/-- Rotated on every use. The stamp is what the store's compare-and-set is conditioned on. -/
def rotate (now : Timestamp) {tenant : TenantId} (token : RefreshToken tenant) :
    Except GrantRejection (RefreshToken tenant) :=
  -- Replacement is tested before revocation, because presenting a token that has already been
  -- exchanged is a replay whatever else is true of it, and a replay is what takes the grant.
  if token.replacedAt.isSome then .error .alreadyRedeemed
  else if token.revokedAt.isSome then .error .revoked
  else if token.expiresAt ≤ now then .error .expired
  else .ok { token with replacedAt := some now }

/-- What the refreshed token may carry. RFC 6749 §6 lets a client ask for less than it was
granted and never for more, and RFC 8707 §2 binds a refresh to the resource its grant named. -/
def entitlement {tenant : TenantId} (token : RefreshToken tenant)
    (requestedScopes : Option (List Scope)) (resource : ResourceIndicator) :
    Except GrantRejection (Entitlement tenant) :=
  if token.resource != resource then .error .resourceMismatch
  else
    let scopes := requestedScopes.getD token.scopes
    if !Scope.subset scopes token.scopes then .error .scopeExceeded
    else
      .ok
        { grant := token.grant
          account := token.account
          client := token.client
          resource := token.resource
          scopes }

end RefreshToken

namespace AccessToken

/-- Why a presented token was not accepted. `wrongAudience` is separate because it is the one
the MCP specification is emphatic about: a resource server that accepts a token issued for
somewhere else is the confused deputy. -/
inductive Rejection where
  | unknown
  | expired
  | revoked
  | wrongAudience
  | insufficientScope (needed : List Scope)
  deriving DecidableEq, Repr, Inhabited

/-- Whether this token may be used at `audience` for an operation needing `required`. -/
def admits {tenant : TenantId} (token : AccessToken tenant) (now : Timestamp)
    (audience : ResourceIndicator) (required : List Scope) : Except Rejection (AccessToken tenant) :=
  if token.revokedAt.isSome then .error .revoked
  else if token.expiresAt ≤ now then .error .expired
  else if token.resource != audience then .error .wrongAudience
  else
    let needed := Scope.missing required token.scopes
    if needed.isEmpty then .ok token else .error (.insufficientScope needed)

end AccessToken

end Authentication.OAuth
