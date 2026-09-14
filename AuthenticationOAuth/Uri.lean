/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Authentication.Url
public import Std.Http.Data.URI

/-!
The URI comparisons the protocol depends on (§20.7, §20.8).

Redirect URI matching is where an authorisation server gives away authorisation codes, so the
comparison is simple string equality on the whole URI (RFC 3986 §6.2.1), with exactly one
exception: a native client binds an ephemeral loopback port at the moment it asks, so RFC 8252
§7.3 requires the port to be ignored there and only there.

The splitting below is deliberately small rather than a general RFC 3986 parser. What matters
is that the loopback exception cannot be reached by any host that is not a loopback address,
and that is a property of a function short enough to prove it about.
-/

@[expose] public section

namespace Authentication.OAuth.Uri


/-- A loopback redirect, split so that the port is the only thing not compared. -/
structure Loopback where
  host : String
  rest : String
  deriving DecidableEq, Repr, Inhabited

def loopback? (uri : String) : Option Loopback :=
  match Url.parts? uri with
  | none => none
  | some parts =>
    if parts.scheme != "http" then none
    else
      match Url.hostAndPort? parts.authority with
      | none => none
      | some (host, port) =>
        if Url.loopbackHosts.contains host && Url.isPort port then
          some { host, rest := parts.rest }
        else none

/-- Simple string comparison, which is what OAuth 2.1 §4.1.1 requires of every redirect URI
that is not a loopback one. -/
def exact (registered presented : String) : Bool := registered == presented

/-- The loopback exception, and nothing else: both sides have to be loopback URIs, and
everything except the port still has to be equal. -/
def matchesIgnoringPort (registered presented : String) : Bool :=
  match loopback? registered, loopback? presented with
  | some r, some p => r.host == p.host && r.rest == p.rest
  | _, _ => false

def admits (registered presented : String) : Bool :=
  exact registered presented || matchesIgnoringPort registered presented

def permits (registered : List String) (presented : String) : Bool :=
  registered.any (admits · presented)

/-- Every redirect URI is `https` or a loopback `http`, and none carries a fragment: RFC 6749
§3.1.2 forbids one, and the MCP security considerations require the rest. -/
def isPermittedRedirect (uri : String) : Bool :=
  if uri.toList.contains '#' then false
  else
    match Url.parts? uri with
    | none => false
    | some parts =>
      match Url.hostAndPort? parts.authority with
      | none => false
      | some (host, port) =>
        !host.isEmpty && Url.isPort port &&
          (parts.scheme == "https" || (loopback? uri).isSome)


def encodeComponent (value : String) : String :=
  toString (Std.Http.URI.EncodedString.encode (r := Std.Http.Internal.Char.isUnreserved) value)

/-- Adds the authorization response's parameters to the client's redirect URI. They go in the
query (RFC 6749 §4.1.2), and they are appended rather than substituted, because a registered
redirect URI is entitled to a query of its own. -/
def withQuery (uri : String) (params : List (String × String)) : String :=
  if params.isEmpty then uri
  else
    let separator := if uri.toList.contains '?' then "&" else "?"
    uri ++ separator ++
      String.intercalate "&"
        (params.map fun (name, value) => encodeComponent name ++ "=" ++ encodeComponent value)

end Authentication.OAuth.Uri

namespace Authentication.OAuth

/-- What a token is for (RFC 8707 §2). Its value is the audience of every token issued against
it, and the check a resource server makes is equality with this. -/
structure ResourceIndicator where
  value : String
  deriving DecidableEq, Repr, Inhabited

namespace ResourceIndicator

/--
An absolute URI with an authority and no fragment.

The scheme and the authority are folded to lower case, which is the robustness the MCP
specification asks for; nothing after the authority is touched, because a path is case
sensitive and a resource server that distinguishes two of them is entitled to.
-/
def parse? (raw : String) : Option ResourceIndicator :=
  if raw.toList.contains '#' then none
  else
    match Url.parts? raw with
    | none => none
    | some parts =>
      match Url.hostAndPort? parts.authority with
      | none => none
      | some (host, _) =>
        if host.isEmpty then none
        else some ⟨parts.scheme ++ "://" ++ parts.authority.toLower ++ parts.rest⟩

end ResourceIndicator

end Authentication.OAuth
