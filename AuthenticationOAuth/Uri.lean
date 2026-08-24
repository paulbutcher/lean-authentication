/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

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

/-- Scheme, authority and everything after it. The scheme is folded to lower case because
schemes are case insensitive; nothing else is normalised. -/
structure Parts where
  scheme : String
  authority : String
  /-- From the first `/`, `?` or `#`, so a URI with no path has none rather than an invented
  one. -/
  rest : String
  deriving DecidableEq, Repr, Inhabited

/-- Splits `scheme://authority<rest>`. Anything that is not in that form, which includes every
URI with no authority, is not something this file has an opinion about. -/
def parts? (uri : String) : Option Parts :=
  let characters := uri.toList
  let scheme := characters.takeWhile (· != ':')
  let tail := characters.dropWhile (· != ':')
  if !(scheme.head?.map (·.isAlpha)).getD false then none
  else if !scheme.all (fun c => c.isAlphanum || c == '+' || c == '-' || c == '.') then none
  else
    match tail with
    | ':' :: '/' :: '/' :: after =>
      let stop := fun (c : Char) => c == '/' || c == '?' || c == '#'
      some
        { scheme := String.ofList (scheme.map Char.toLower)
          authority := String.ofList (after.takeWhile (!stop ·))
          rest := String.ofList (after.dropWhile (!stop ·)) }
    | _ => none

/-- The host and whatever followed it, which is either nothing or a port. An authority carrying
user information is rejected outright: `https://trusted.example@evil.test/` reads as the trusted
host to a person and resolves to the other one. -/
def hostAndPort? (authority : String) : Option (String × String) :=
  let characters := authority.toList
  if characters.contains '@' then none
  else if authority.startsWith "[" then
    match characters.dropWhile (· != ']') with
    | [] => none
    | _ :: after =>
      some (String.ofList (characters.takeWhile (· != ']') ++ [']']), String.ofList after)
  else
    some (String.ofList (characters.takeWhile (· != ':')),
      String.ofList (characters.dropWhile (· != ':')))

/-- Either nothing, or a colon and at least one digit. -/
def isPort (suffix : String) : Bool :=
  suffix.isEmpty || (suffix.startsWith ":" && 1 < suffix.length && (suffix.drop 1).all Char.isDigit)

/--
The hosts a redirect may vary its port on.

RFC 8252 §7.3 names only the IP literals, and §8.3 recommends against `localhost` because it
resolves through the host's own configuration and may not be the loopback interface. It is
admitted here regardless, because the metadata document in the MCP specification's own example
registers one, and a client whose redirect URI cannot be matched cannot connect at all.
-/
def loopbackHosts : List String := ["127.0.0.1", "[::1]", "localhost"]

/-- A loopback redirect, split so that the port is the only thing not compared. -/
structure Loopback where
  host : String
  rest : String
  deriving DecidableEq, Repr, Inhabited

def loopback? (uri : String) : Option Loopback :=
  match parts? uri with
  | none => none
  | some parts =>
    if parts.scheme != "http" then none
    else
      match hostAndPort? parts.authority with
      | none => none
      | some (host, port) =>
        if loopbackHosts.contains host && isPort port then
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
    match parts? uri with
    | none => false
    | some parts =>
      match hostAndPort? parts.authority with
      | none => false
      | some (host, port) =>
        !host.isEmpty && isPort port &&
          (parts.scheme == "https" || (loopback? uri).isSome)

/-- Hosts a metadata document is never fetched from. The document is fetched by this server on
whatever the caller wrote, which is a server-side request forgery if the caller can name the
network the server is on rather than the internet (client ID metadata document draft §6.5). -/
def isPrivateHost (host : String) : Bool :=
  let lower := host.toLower
  loopbackHosts.contains lower || lower == "0.0.0.0" || lower == "[::]" ||
    lower.endsWith ".localhost" || lower.endsWith ".local" || lower.endsWith ".internal" ||
    lower.startsWith "10." || lower.startsWith "192.168." || lower.startsWith "169.254." ||
    lower.startsWith "127." || lower.startsWith "[fd" || lower.startsWith "[fc" ||
    lower.startsWith "[fe80:" ||
    (lower.startsWith "172." &&
      (List.range 16).any fun n => lower.startsWith s!"172.{n + 16}.")

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
    match Uri.parts? raw with
    | none => none
    | some parts =>
      match Uri.hostAndPort? parts.authority with
      | none => none
      | some (host, _) =>
        if host.isEmpty then none
        else some ⟨parts.scheme ++ "://" ++ parts.authority.toLower ++ parts.rest⟩

end ResourceIndicator

end Authentication.OAuth
