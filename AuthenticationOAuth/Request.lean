/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import AuthenticationOAuth.Error
public import AuthenticationOAuth.Grant

/-!
Reading the two request formats (§20.4).

The authorization request arrives as query parameters and the token request as an
`application/x-www-form-urlencoded` body, and both reach here already decoded, as name and value
pairs. The registration request is JSON and is read in `Registration`; keeping the two apart is
the point of their being separate files, because a parser that accepted either would accept a
form-encoded registration and a JSON token request, and neither is a thing this server has
agreed to read.

The authorization request is read in two stages, because where an error goes is decided by
parameters that may themselves be wrong. Until the client and its redirect URI are settled,
nothing can be reported to the client at all.
-/

public section

namespace Authentication.OAuth

/-- Names and values, decoded by whatever received the request. -/
abbrev Params := List (String × String)

namespace Params

/-- A parameter sent more than once is `invalid_request` (OAuth 2.1 §4.1.1). -/
def single? (params : Params) (name : String) : Except OAuthError (Option String) :=
  match params.filter (·.1 == name) with
  | [] => .ok none
  | [(_, value)] => .ok (some value)
  | _ => .error .invalidRequest

def required (params : Params) (name : String) : Except OAuthError String := do
  match ← params.single? name with
  | none => .error .invalidRequest
  | some value => .ok value

def present (params : Params) (name : String) : Bool := params.any (·.1 == name)

/-- RFC 8707 §2 gives one code for a resource that is invalid, missing, unknown or malformed,
and a second `resource` is one this server cannot honour rather than one it may narrow, so all
three failures are `invalid_target` rather than `invalid_request`. -/
def requiredResource (params : Params) : Except OAuthError ResourceIndicator :=
  match params.filter (·.1 == "resource") with
  | [(_, raw)] =>
    match ResourceIndicator.parse? raw with
    | none => .error .invalidTarget
    | some resource => .ok resource
  | _ => .error .invalidTarget

end Params

/-- OpenID Connect's `prompt`, read now and mostly acted on later (§20.13). It is here because
the alternative is discovering at the point of adding OpenID Connect that every caller assumed a
session is only ever read. -/
inductive Prompt where
  /-- The `none` value: show no interface at all, and fail rather than ask. Spelled differently
  because `none` is already a constructor of `Option`. -/
  | silent
  | login
  | consent
  | selectAccount
  | unknown (value : String)
  deriving DecidableEq, Repr, Inhabited

namespace Prompt

def ofString : String → Prompt
  | "none" => .silent
  | "login" => .login
  | "consent" => .consent
  | "select_account" => .selectAccount
  | value => .unknown value

def parse (raw : String) : List Prompt :=
  ((raw.splitOn " ").filter (!·.isEmpty)).eraseDups.map ofString

end Prompt

/-- The parameters that decide where an error can be sent, read before anything else. An error
in one of these cannot be reported to the client at all, because reporting it means redirecting
to a URI this server has not established the client owns (OAuth 2.1 §4.1.2.1). -/
structure Addressing where
  clientId : ClientId
  redirectUri : Option String
  state : Option String
  deriving DecidableEq, Repr, Inhabited

def Addressing.parse (params : Params) : Except OAuthError Addressing := do
  pure
    { clientId := ⟨← params.required "client_id"⟩
      redirectUri := ← params.single? "redirect_uri"
      state := ← params.single? "state" }

/-- A validated authorization request, with the redirect URI resolved against the client's
registration. -/
structure AuthorizationRequest where
  clientId : ClientId
  redirectUri : String
  /-- Whether the request named it, which decides whether the token request has to repeat it. -/
  redirectUriGiven : Bool
  state : Option String
  scopes : List Scope
  codeChallenge : String
  resource : ResourceIndicator
  prompt : List Prompt
  /-- Seconds, from OpenID Connect's `max_age`. -/
  maxAge : Option Nat
  deriving DecidableEq, Repr, Inhabited

namespace AuthorizationRequest

def refused {α : Type} (error : OAuthError) (description : String) : Except ErrorResponse α :=
  .error { error, description }

/--
Everything after the redirect URI is settled.

`code_challenge_method` is required rather than defaulted. OAuth 2.1 defaults it to `plain`, and
`plain` is not implemented here, so a request that omits it is one whose author believes it is
protected and is not.
-/
def parse (params : Params) (addressing : Addressing) (redirectUri : String) :
    Except ErrorResponse AuthorizationRequest := do
  let read {α : Type} (result : Except OAuthError α) : Except ErrorResponse α :=
    match result with
    | .error error => .error { error, description := "a parameter was given more than once" }
    | .ok value => .ok value
  let responseType ← read (params.required "response_type")
  if responseType != "code" then
    refused .unsupportedResponseType "only the authorization code response type is supported"
  else
    let challenge ← read (params.required "code_challenge")
    if challenge.isEmpty then refused .invalidRequest "code_challenge is required"
    else
      let method ← read (params.required "code_challenge_method")
      if method != "S256" then
        refused .invalidRequest "code_challenge_method must be S256"
      else
        match params.requiredResource with
        | .error _ =>
          refused .invalidTarget "resource must be a single absolute URI with no fragment"
        | .ok resource =>
          let maxAge ← match ← read (params.single? "max_age") with
            | none => pure none
            | some raw =>
              match raw.toNat? with
              | none => refused .invalidRequest "max_age must be a whole number of seconds"
              | some seconds => pure (some seconds)
          pure
            { clientId := addressing.clientId
              redirectUri
              redirectUriGiven := addressing.redirectUri.isSome
              state := addressing.state
              scopes := Scope.parse ((← read (params.single? "scope")).getD "")
              codeChallenge := challenge
              resource
              prompt := Prompt.parse ((← read (params.single? "prompt")).getD "")
              maxAge }

end AuthorizationRequest

/-- The two grant types this server issues tokens for, and no others: no implicit, no hybrid, no
password, no client credentials. -/
inductive TokenGrant where
  | authorizationCode (code : String) (redirectUri : Option String) (verifier : String)
  | refresh (token : String) (scopes : Option (List Scope))
  deriving DecidableEq, Repr, Inhabited

structure TokenRequest where
  clientId : ClientId
  resource : ResourceIndicator
  grant : TokenGrant
  deriving DecidableEq, Repr, Inhabited

namespace TokenRequest

/-- Client authentication this server has no way to perform. Every client here is public and
authenticates with `none`, so a request offering a secret is offering one nobody issued. -/
def authenticationAttempted (params : Params) : Bool :=
  params.present "client_secret" || params.present "client_assertion" ||
    params.present "client_assertion_type"

def parse (params : Params) : Except ErrorResponse TokenRequest := do
  let read {α : Type} (result : Except OAuthError α) : Except ErrorResponse α :=
    match result with
    | .error error => .error { error, description := "a parameter was given more than once" }
    | .ok value => .ok value
  if authenticationAttempted params then
    .error { error := .invalidClient, description := "this server registers no client secrets" }
  else
    let clientId : ClientId := ⟨← read (params.required "client_id")⟩
    match params.requiredResource with
    | .error _ =>
      .error
        { error := .invalidTarget
          description := "resource must be a single absolute URI with no fragment" }
    | .ok resource =>
      let grant ← match ← read (params.required "grant_type") with
        | "authorization_code" =>
          let verifier ← read (params.required "code_verifier")
          if !Pkce.isVerifier verifier then
            .error
              { error := .invalidRequest
                description := "code_verifier must be 43 to 128 unreserved characters" }
          else
            pure (TokenGrant.authorizationCode (← read (params.required "code"))
              (← read (params.single? "redirect_uri")) verifier)
        | "refresh_token" =>
          pure (TokenGrant.refresh (← read (params.required "refresh_token"))
            ((← read (params.single? "scope")).map Scope.parse))
        | _ =>
          .error
            { error := .unsupportedGrantType
              description := "only authorization_code and refresh_token are supported" }
      pure { clientId, resource, grant }

end TokenRequest

end Authentication.OAuth
