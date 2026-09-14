/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Authentication
public import AuthenticationFetch
public import Jose
public import Json

/-!
The provider's discovery document, and what goes wrong reaching it (AUTH-6.4).
-/

public section

namespace Authentication.Oidc

inductive OidcError where
  | fetch (reason : Fetch.FetchError)
  | badDocument (field : String)
  /-- The document named an issuer other than the one it was fetched for. OpenID Connect
  Discovery §4.3 requires the check, and it is the one that stops a provider this tenant
  configured being impersonated by a document served from somewhere else. -/
  | issuerMismatch (expected actual : String)
  | token (reason : Jose.Error)
  /-- The ID token carried no `nonce`, or not the one this sign-in sent (AUTH-6.3). -/
  | nonceMismatch
  /-- No `sub`, so there is no stable key to link on (AUTH-6.6). -/
  | subjectMissing
  /-- An unknown `kid` asked for a refetch too soon after the last one (AUTH-6.4). -/
  | refetchThrottled
  deriving Repr

/-- The operator's name for one, for a log record or a span attribute. -/
def OidcError.name : OidcError → String
  | .fetch _ => "fetch-failed"
  | .badDocument _ => "bad-document"
  | .issuerMismatch _ _ => "issuer-mismatch"
  | .token _ => "token-rejected"
  | .nonceMismatch => "nonce-mismatch"
  | .subjectMissing => "subject-missing"
  | .refetchThrottled => "refetch-throttled"

/-- What this library uses out of the discovery document. A provider publishes a great deal more
and none of it is read, because a field nothing acts on is a field nobody has checked. -/
structure Discovery where
  issuer : String
  authorizationEndpoint : String
  tokenEndpoint : String
  jwksUri : String
  deriving Repr, Inhabited

/-- OpenID Connect Discovery §4: the suffix goes after the issuer, whose trailing slash is not
part of it. An issuer carrying a path keeps it, which is what distinguishes this from RFC 8414's
placement and is what the providers in AUTH-6.9 actually serve. -/
def wellKnownUrl (issuer : String) : String :=
  let trimmed := String.ofList (issuer.toList.reverse.dropWhile (· == '/')).reverse
  trimmed ++ "/.well-known/openid-configuration"

private def stringField (document : Json) (name : String) : Except OidcError String :=
  match (document.getObjVal? name).toOption.bind (·.getStr?.toOption) with
  | some value => .ok value
  | none => .error (.badDocument name)

/--
Reads the document, and refuses one that names an issuer other than the one asked for.

Every endpoint is then checked by `Fetch.permitted` when it is used, so nothing here has to
decide whether a URL is safe to reach; what it decides is whether the document is this provider's
at all.
-/
def readDiscovery (expected : String) (body : String) : Except OidcError Discovery := do
  let document ← match Json.parse body with
    | .ok value => pure value
    | .error _ => throw (.badDocument "json")
  let issuer ← stringField document "issuer"
  if issuer != expected then throw (.issuerMismatch expected issuer)
  pure
    { issuer
      authorizationEndpoint := ← stringField document "authorization_endpoint"
      tokenEndpoint := ← stringField document "token_endpoint"
      jwksUri := ← stringField document "jwks_uri" }

end Authentication.Oidc
