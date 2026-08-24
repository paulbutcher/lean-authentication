/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import AuthenticationOAuth.Client
public import AuthenticationOAuth.Error

/-!
The registration endpoint of RFC 7591 (AUTH-20.6.5).

Deprecated by the MCP specification and retained by it for at least twelve months, which is why
it is here: a client that has not implemented metadata documents yet has no other way to obtain
an identifier, and refusing it means refusing the client.

The body is JSON, and the token endpoint's is form encoded. Nothing here reads a form and
nothing in `Request` reads JSON, which is the whole of how the two are kept from being confused.
-/

public section

namespace Authentication.OAuth.Registration

/-- RFC 7591 §3.2.2 gives the endpoint two codes: one for the redirect URIs and one for
everything else. -/
def rejection : MetadataRejection → ErrorResponse
  | .notAnObject =>
    { error := .invalidClientMetadata, description := "the request body is not a JSON object" }
  | .clientIdMismatch =>
    { error := .invalidClientMetadata, description := "client_id is not a registration request" }
  | .missingName =>
    { error := .invalidClientMetadata, description := "client_name is required" }
  | .missingRedirectUris =>
    { error := .invalidRedirectUri, description := "redirect_uris is required and may not be empty" }
  | .unusableRedirectUri =>
    { error := .invalidRedirectUri
      description := "every redirect URI must be https or loopback http, and carry no fragment" }
  | .unsupportedAuthMethod =>
    { error := .invalidClientMetadata, description := "token_endpoint_auth_method must be none" }
  | .unsupportedGrantType =>
    { error := .invalidClientMetadata
      description := "only the authorization_code and refresh_token grant types are supported" }
  | .unsupportedResponseType =>
    { error := .invalidClientMetadata, description := "only the code response type is supported" }

/-- RFC 7591 §3.2.1. There is no `client_secret` and no `client_secret_expires_at`: every client
here is public and authenticates with `none`, and a secret nobody can use is a secret that leaks
for nothing. -/
def response {tenant : TenantId} (record : ClientRecord tenant) : Json :=
  Json.mkObj
    (ClientMetadata.fields record.id record.metadata ++
      [("client_id_issued_at", Json.ofInt record.registeredAt.epochSeconds)])

def createdStatus : Nat := 201

end Authentication.OAuth.Registration
