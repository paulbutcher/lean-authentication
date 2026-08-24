/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Authentication.Tenant
public import Authentication.Time
public import AuthenticationOAuth.Uri
public import Json

/-!
Clients, and the two ways one comes to exist (§20.6).

A client identifier is either an `https` URL that resolves to a metadata document the client
hosts, or a string this server issued at its registration endpoint. Which of the two a given
identifier is, is decided by looking at it, and by nothing else: a client that registered
dynamically cannot later be resolved as a URL, and a URL is never looked for in the
registrations table.

The metadata is the same shape either way, which is the point. Everything downstream of
resolution, redirect matching, the consent page, the code and the tokens, sees a client and not
a mechanism.
-/

@[expose] public section

namespace Authentication.OAuth

structure ClientId where
  value : String
  deriving DecidableEq, Repr, Inhabited

/-- The registration metadata registry of RFC 7591 §2, restricted to what this server acts on.
Anything else in a document is ignored rather than refused, which is what lets a client publish
one document for several authorisation servers. -/
structure ClientMetadata where
  clientName : String := ""
  redirectUris : List String := []
  clientUri : Option String := none
  logoUri : Option String := none
  scope : Option String := none
  grantTypes : List String := ["authorization_code", "refresh_token"]
  responseTypes : List String := ["code"]
  tokenEndpointAuthMethod : String := "none"
  /-- Recorded and not enforced. It constrains redirect URIs only under OpenID Connect
  registration, which this is not, and the MCP client registration page says a non-OIDC server
  safely ignores it. Refusing a native client that omitted it would break exactly the clients
  the loopback rule exists for. -/
  applicationType : Option String := none
  softwareId : Option String := none
  softwareVersion : Option String := none
  deriving DecidableEq, Repr, Inhabited

inductive ClientOrigin where
  | metadataDocument
  | dynamic
  deriving DecidableEq, Repr, Inhabited

/-- A client the flow can act on: resolved, validated, and no longer carrying which mechanism
produced it except where the consent page has to say. -/
structure Client where
  id : ClientId
  metadata : ClientMetadata
  origin : ClientOrigin
  deriving DecidableEq, Repr, Inhabited

/-- Why a document or a registration request was refused. The distinctions exist because
RFC 7591 §3.2.2 gives the registration endpoint two codes and the operator one question:
whether it was the URIs or everything else. -/
inductive MetadataRejection where
  | notAnObject
  | clientIdMismatch
  | missingName
  | missingRedirectUris
  /-- Not `https`, not a loopback `http`, or carrying a fragment. -/
  | unusableRedirectUri
  /-- Anything but `none`. A shared symmetric secret is forbidden outright for a metadata
  document (client ID metadata document draft §6.2), and `private_key_jwt` needs a JWKS, which
  arrives with OpenID Connect. -/
  | unsupportedAuthMethod
  | unsupportedGrantType
  | unsupportedResponseType
  deriving DecidableEq, Repr, Inhabited

namespace ClientMetadata

def grantTypesSupported : List String := ["authorization_code", "refresh_token"]

def responseTypesSupported : List String := ["code"]

def stringField? (document : Json) (name : String) : Option String :=
  match (document.getObjVal? name).toOption with
  | some (.str value) => some value
  | _ => none

def stringsField? (document : Json) (name : String) : Option (List String) :=
  match (document.getObjVal? name).toOption with
  | some (.arr elements) =>
    elements.toList.foldr
      (fun element acc =>
        match element, acc with
        | .str value, some rest => some (value :: rest)
        | _, _ => none)
      (some [])
  | _ => none

/--
Reads and validates a document. `requireName` is set for a metadata document, where the MCP
client registration page requires `client_name` so that the consent page has something to show,
and clear for a registration request, where RFC 7591 makes every field optional.
-/
def ofJson (document : Json) (requireName : Bool) : Except MetadataRejection ClientMetadata := do
  match document with
  | .obj _ => pure ()
  | _ => throw .notAnObject
  let clientName := (stringField? document "client_name").getD ""
  if requireName && clientName.isEmpty then throw .missingName
  let redirectUris ← match stringsField? document "redirect_uris" with
    | none => throw .missingRedirectUris
    | some [] => throw .missingRedirectUris
    | some uris => pure uris
  if !redirectUris.all Uri.isPermittedRedirect then throw .unusableRedirectUri
  let method := (stringField? document "token_endpoint_auth_method").getD "none"
  if method != "none" then throw .unsupportedAuthMethod
  let grantTypes := (stringsField? document "grant_types").getD ["authorization_code"]
  if !grantTypes.all grantTypesSupported.contains then throw .unsupportedGrantType
  let responseTypes := (stringsField? document "response_types").getD ["code"]
  if !responseTypes.all responseTypesSupported.contains then throw .unsupportedResponseType
  pure
    { clientName
      redirectUris
      clientUri := stringField? document "client_uri"
      logoUri := stringField? document "logo_uri"
      scope := stringField? document "scope"
      grantTypes
      responseTypes
      tokenEndpointAuthMethod := method
      applicationType := stringField? document "application_type"
      softwareId := stringField? document "software_id"
      softwareVersion := stringField? document "software_version" }

def optional (name : String) : Option String → List (String × Json)
  | none => []
  | some value => [(name, Json.str value)]

/-- What the registration endpoint echoes back, and what the store holds. RFC 7591 §3.2.1
requires the response to carry every field that was registered. -/
def fields (id : ClientId) (metadata : ClientMetadata) : List (String × Json) :=
  [ ("client_id", Json.str id.value),
    ("client_name", Json.str metadata.clientName),
    ("redirect_uris", Json.arr (metadata.redirectUris.map Json.str).toArray),
    ("grant_types", Json.arr (metadata.grantTypes.map Json.str).toArray),
    ("response_types", Json.arr (metadata.responseTypes.map Json.str).toArray),
    ("token_endpoint_auth_method", Json.str metadata.tokenEndpointAuthMethod) ]
  ++ optional "client_uri" metadata.clientUri
  ++ optional "logo_uri" metadata.logoUri
  ++ optional "scope" metadata.scope
  ++ optional "application_type" metadata.applicationType
  ++ optional "software_id" metadata.softwareId
  ++ optional "software_version" metadata.softwareVersion

def toJson (id : ClientId) (metadata : ClientMetadata) : Json := Json.mkObj (fields id metadata)

end ClientMetadata

namespace ClientId

/--
Where a client identifier is to be resolved.

`rejected` is not the same as `dynamic`: an identifier that is a URL but not a usable metadata
document URL must not fall through to the registrations table, or an attacker who can register
dynamically chooses what a URL-shaped identifier means.
-/
inductive Registration where
  | metadataDocument (url : String)
  | dynamic
  | rejected
  deriving DecidableEq, Repr, Inhabited

/--
The rules the client ID metadata document draft §3 states: `https`, a path component, no dot
segments, no fragment, no user information.

The private-address refusal is §6.5's: this server fetches whatever the identifier names, so an
identifier naming the network the server is on rather than the internet is a request forgery
with the server as the deputy.
-/
def metadataDocumentUrl? (id : ClientId) : Option String :=
  if id.value.toList.contains '#' then none
  else
    match Uri.parts? id.value with
    | none => none
    | some parts =>
      if parts.scheme != "https" then none
      else
        match Uri.hostAndPort? parts.authority with
        | none => none
        | some (host, port) =>
          if host.isEmpty || !Uri.isPort port || Uri.isPrivateHost host then none
          else
            let path := String.ofList (parts.rest.toList.takeWhile (· != '?'))
            if !path.startsWith "/" || path.length < 2 then none
            else if (path.splitOn "/").any (fun segment => segment == "." || segment == "..") then
              none
            else some id.value

def registration (id : ClientId) : Registration :=
  match Uri.parts? id.value with
  | none => .dynamic
  | some _ =>
    match metadataDocumentUrl? id with
    | some url => .metadataDocument url
    | none => .rejected

/-- What the consent page has to display beside the client's own name (client ID metadata
document draft §6.4). -/
def host? (id : ClientId) : Option String :=
  match Uri.parts? id.value with
  | none => none
  | some parts => (Uri.hostAndPort? parts.authority).map (·.1)

end ClientId

/--
Reads a fetched metadata document as a client.

The identifier check is the whole security of the mechanism: without it, any client could name
any document and be taken for whoever published it.
-/
def clientOfDocument (id : ClientId) (document : Json) : Except MetadataRejection Client := do
  match ClientMetadata.stringField? document "client_id" with
  | some declared => if declared != id.value then throw .clientIdMismatch
  | none => throw .clientIdMismatch
  pure { id, metadata := ← ClientMetadata.ofJson document true, origin := .metadataDocument }

/-- A client that registered dynamically. They accumulate, one per fresh connection from some
clients, which is why `lastUsedAt` is here and why the store can prune on it. -/
structure ClientRecord (tenant : TenantId) where
  id : ClientId
  metadata : ClientMetadata
  registeredAt : Timestamp
  lastUsedAt : Timestamp
  deriving DecidableEq, Repr

/-- A metadata document held for as long as the response that carried it said it was good for.
Nothing malformed and no error reaches here: the draft forbids caching either. -/
structure CachedDocument (tenant : TenantId) where
  client : ClientId
  metadata : ClientMetadata
  fetchedAt : Timestamp
  freshUntil : Timestamp
  deriving DecidableEq, Repr

end Authentication.OAuth
