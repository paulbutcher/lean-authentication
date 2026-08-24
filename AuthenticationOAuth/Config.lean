/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Authentication.Config
public import AuthenticationOAuth.Scope

/-!
What varies by deployment (§20.3).

Per tenant, like everything else here, because the issuer identifier is per tenant: tenants are
distinguished by a path prefix on one origin (AUTH-4.3.2), and RFC 8414 §3 inserts the
well-known suffix ahead of an issuer's path, so a tenant's metadata document is reachable
without a hostname of its own.
-/

public section

namespace Authentication.OAuth

/-- Everything an authorisation server has to be told. Every duration has a default that is
defensible and none of them is a secret, so a deployment that sets only the endpoints is
running the configuration this library would argue for. -/
structure OAuthConfig (tenant : TenantId) where
  /-- RFC 8414 §2 and RFC 9207 §2: an `https` URL with no query and no fragment. It is what the
  `iss` parameter carries on every authorization response, and a client compares it by simple
  string comparison against what discovery gave it, so it is written once here and never
  rebuilt. -/
  issuer : String
  authorizationEndpoint : String
  tokenEndpoint : String
  registrationEndpoint : String
  /-- The scopes the metadata document advertises. RFC 9728 calls this the minimal set for
  basic functionality; a resource server names anything more in its own challenge. -/
  scopesSupported : List Scope := []
  /-- OAuth 2.1 §4.1.3 recommends at most ten minutes. A code is redeemed by a program that has
  just received it, so a minute is generous. -/
  authorizationCodeLifetime : Duration := Duration.minutes 10
  /-- Short, because the MCP security considerations ask for short: a leaked access token is
  usable until it expires and there is nothing to consult that would say otherwise. -/
  accessTokenLifetime : Duration := Duration.hours 1
  refreshTokenLifetime : Duration := Duration.days 30
  /-- Whether refresh tokens are issued at all. RFC 6749 §1.5 leaves it to the server, and a
  deployment where every client is short-lived is entitled to say no. -/
  refreshTokensEnabled : Bool := true
  /-- The longest a fetched metadata document is held, whatever its own cache headers said.
  The client ID metadata document draft §5 lets the server define its own bounds. -/
  clientDocumentMaxAge : Duration := Duration.hours 24
  /-- How long a document is held when the response said nothing about freshness. -/
  clientDocumentDefaultAge : Duration := Duration.minutes 15
  /-- Five kilobytes, which is what the draft §6.6 recommends. -/
  clientDocumentMaxBytes : Nat := 5120

namespace OAuthConfig

/-- The endpoints below the tenant's own path, which is where a deployment that has not moved
them will put them. -/
def standard {tenant : TenantId} (base : BaseUrl) (scopesSupported : List Scope := []) :
    OAuthConfig tenant :=
  { issuer := (base.url tenant "").value
    authorizationEndpoint := (base.url tenant "/oauth/authorize").value
    tokenEndpoint := (base.url tenant "/oauth/token").value
    registrationEndpoint := (base.url tenant "/oauth/register").value
    scopesSupported }

end OAuthConfig

end Authentication.OAuth
