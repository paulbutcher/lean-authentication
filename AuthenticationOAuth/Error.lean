/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Json

/-!
The error codes of OAuth 2.1 §4.1.2.1 and §5.3, RFC 6750 §3.1, RFC 7591 §3.2.2 and RFC 8707 §2
(§20.11).

One type for all of them, because the same rejection reaches a client in three different
shapes: as query parameters on a redirect, as a JSON body, and as `WWW-Authenticate`
parameters. Deciding the code in one place and the shape at the edge is what keeps those three
agreeing.

`description` is never anything the caller sent. An error description is copied into a redirect
and shown to a person, and one that echoed a parameter would be a channel from whoever crafted
the request to whoever is reading the page.
-/

public section

namespace Authentication.OAuth

inductive OAuthError where
  | invalidRequest
  | invalidClient
  | invalidGrant
  | unauthorizedClient
  | unsupportedGrantType
  | unsupportedResponseType
  | invalidScope
  /-- RFC 8707 §2: the `resource` is missing, unknown, or malformed. -/
  | invalidTarget
  | accessDenied
  /-- Reserved for `prompt=none` (§20.13). Nothing issues it while OIDC is out, and the code
  exists so that the path which will is already spelled. -/
  | loginRequired
  | consentRequired
  | interactionRequired
  /-- RFC 7591 §3.2.2, at the registration endpoint only. -/
  | invalidRedirectUri
  | invalidClientMetadata
  /-- RFC 6750 §3.1, at a resource server rather than here. -/
  | insufficientScope
  | serverError
  | temporarilyUnavailable
  deriving DecidableEq, Repr, Inhabited

namespace OAuthError

def code : OAuthError → String
  | invalidRequest => "invalid_request"
  | invalidClient => "invalid_client"
  | invalidGrant => "invalid_grant"
  | unauthorizedClient => "unauthorized_client"
  | unsupportedGrantType => "unsupported_grant_type"
  | unsupportedResponseType => "unsupported_response_type"
  | invalidScope => "invalid_scope"
  | invalidTarget => "invalid_target"
  | accessDenied => "access_denied"
  | loginRequired => "login_required"
  | consentRequired => "consent_required"
  | interactionRequired => "interaction_required"
  | invalidRedirectUri => "invalid_redirect_uri"
  | invalidClientMetadata => "invalid_client_metadata"
  | insufficientScope => "insufficient_scope"
  | serverError => "server_error"
  | temporarilyUnavailable => "temporarily_unavailable"

/-- The status a JSON error response carries. `invalid_client` is 401 rather than 400 because
that is what OAuth 2.1 §5.3 requires whenever the request carried client credentials, and this
server never has to distinguish: it authenticates no client, so every `invalid_client` is a
client it could not identify at all. -/
def status : OAuthError → Nat
  | invalidClient => 401
  | insufficientScope => 403
  | serverError => 500
  | temporarilyUnavailable => 503
  | _ => 400

end OAuthError

/-- A code and the fixed phrase that goes with it. -/
structure ErrorResponse where
  error : OAuthError
  description : String := ""
  deriving DecidableEq, Repr, Inhabited

namespace ErrorResponse

def status (e : ErrorResponse) : Nat := e.error.status

/-- The form both the redirect and the `WWW-Authenticate` header are built from. -/
def params (e : ErrorResponse) : List (String × String) :=
  ("error", e.error.code) ::
    (if e.description.isEmpty then [] else [("error_description", e.description)])

def toJson (e : ErrorResponse) : Json := Json.mkObj (e.params.map fun (k, v) => (k, Json.str v))

end ErrorResponse

end Authentication.OAuth
