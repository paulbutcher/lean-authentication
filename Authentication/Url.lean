/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

/-!
As much of a URL as deciding whether to fetch it needs.

Both directions of §6 and §20 fetch a URL somebody else chose, and the rules for refusing one are
the same rules (AUTH-6.13). They are here, once, rather than in each of the targets that fetches,
so that a range added to `isPrivateHost` protects both.
-/

public section

namespace Authentication.Url

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
end Authentication.Url
