/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import AuthenticationOAuth.Config
public import Json

/-!
The authorisation server metadata document of RFC 8414 §2 (§20.12).

Serving it is the caller's: it belongs at `/.well-known/oauth-authorization-server`, with the
issuer's path inserted after the suffix, and where a route lives is not this library's business.
What is here is the document.

Four of its fields are what a client reads to decide how to talk to this server at all.
`code_challenge_methods_supported` is how PKCE support is discovered, and a client that does not
find it must refuse to proceed; `client_id_metadata_document_supported` together with `"none"` in
`token_endpoint_auth_methods_supported` is how a client decides it may use a URL as its
identifier; and `authorization_response_iss_parameter_supported` is what makes a missing `iss` a
reason to reject the response rather than to shrug.

None of the four is configurable, because none of them describes a choice a deployment has.
-/

@[expose] public section

namespace Authentication.OAuth

def metadataDocument {tenant : TenantId} (config : OAuthConfig tenant) : Json :=
  Json.mkObj
    [ ("issuer", .str config.issuer),
      ("authorization_endpoint", .str config.authorizationEndpoint),
      ("token_endpoint", .str config.tokenEndpoint),
      ("registration_endpoint", .str config.registrationEndpoint),
      ("scopes_supported",
        .arr (config.scopesSupported.map fun scope => Json.str scope.value).toArray),
      ("response_types_supported", .arr #[.str "code"]),
      ("response_modes_supported", .arr #[.str "query"]),
      ("grant_types_supported", .arr #[.str "authorization_code", .str "refresh_token"]),
      ("token_endpoint_auth_methods_supported", .arr #[.str "none"]),
      ("code_challenge_methods_supported", .arr #[.str "S256"]),
      ("client_id_metadata_document_supported", .bool true),
      ("authorization_response_iss_parameter_supported", .bool true) ]

end Authentication.OAuth
