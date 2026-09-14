/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Authentication.Time
public import Authentication.Url
public import Leancurl

/-!
Fetching a document somebody else named (AUTH-6.12, AUTH-6.13).

This target knows nothing of OIDC, and nothing of the authorisation server. What it knows is that
a URL reached this process because a stranger put it somewhere, and what the rules are for
refusing one: `https` only, no private or loopback address, a bounded timeout, a bounded body,
and no redirect to a host that would not have been fetched directly.

Those rules live above the `Http` seam rather than inside it, so that a deployment replacing the
transport replaces a transport and not a policy.
-/

public section

namespace Authentication.Fetch

/-- The seam a fake stands in for, as `Postmark.Http` and `Ses.Http` are for their transports.
It is deliberately dumb: every decision worth reviewing is taken above it. -/
structure Http (m : Type → Type) where
  send : Leancurl.Request → m (Except Leancurl.CurlError Leancurl.Response)

def curlHttp : Http IO where
  send := Leancurl.Curl.send

structure Limits where
  /-- A request made on a stranger's say-so must not be able to hold a response open, so the
  timeout is configuration rather than libcurl's default of none at all. -/
  timeoutMs : UInt32 := 5000
  maxBytes : Nat := 65536
  /-- Enough for a provider that moves its document once, and not enough to walk a chain. -/
  maxRedirects : Nat := 3

inductive FetchError where
  | notHttps (url : String)
  | privateAddress (host : String)
  | malformedUrl (url : String)
  | tooManyRedirects
  | redirectWithoutLocation
  | transport (code : UInt32) (message : String)
  | status (code : UInt32)
  | tooLarge (size : Nat)
  deriving DecidableEq, Repr, Inhabited

/-- What was fetched, and the two things about the response that do not survive being parsed:
how long it may be held, and how big it was. -/
structure Document where
  body : String
  freshFor : Option Duration := none
  size : Nat
  deriving Repr

/--
Whether this URL may be fetched at all (AUTH-6.13).

Every refusal here is decided before a packet leaves, which is the point: an address check made
on the response has already made the request it was meant to prevent.
-/
def permitted (url : String) : Except FetchError Unit :=
  match Url.parts? url with
  | none => .error (.malformedUrl url)
  | some parts =>
    if parts.scheme != "https" then .error (.notHttps url)
    else match Url.hostAndPort? parts.authority with
      | none => .error (.malformedUrl url)
      | some (host, port) =>
        if host.isEmpty || !Url.isPort port then .error (.malformedUrl url)
        else if Url.isPrivateHost host then .error (.privateAddress host)
        else .ok ()

/-- Header lookup, case-insensitively: field names are not case sensitive and no provider is
obliged to spell one the way this file would have. -/
def header? (headers : Leancurl.Headers) (name : String) : Option String :=
  let wanted := name.toLower
  (headers.find? fun (key, _) => key.toLower == wanted).map (·.2)

private def digitsOf (text : String) : Option Nat :=
  let digits := text.toList.dropWhile (!·.isDigit) |>.takeWhile (·.isDigit)
  if digits.isEmpty then none else String.toNat? (String.ofList digits)

/-- `max-age` from `Cache-Control`, and nothing else. `Expires` is a date, and reading one means
trusting the two clocks to agree; a provider that offers only `Expires` is treated as a provider
that said nothing, which the caller is free to bound for itself. -/
def freshness (headers : Leancurl.Headers) : Option Duration :=
  match header? headers "cache-control" with
  | none => none
  | some value =>
    let lower := value.toLower
    if (lower.splitOn "no-store").length > 1 then some ⟨0⟩
    else match (lower.splitOn "max-age=").tail? with
      | some (rest :: _) => (digitsOf rest).map (fun n => ⟨n⟩)
      | _ => none

private def isRedirect (status : UInt32) : Bool :=
  status == 301 || status == 302 || status == 303 || status == 307 || status == 308

/-- A relative `Location` resolved against the URL it came from, which is only ever used to
decide where to go next and is checked by `permitted` like any other. -/
private def resolveLocation (origin target : String) : String :=
  if (Url.parts? target).isSome then target
  else match Url.parts? origin with
    | none => target
    | some parts =>
      if target.startsWith "/" then parts.scheme ++ "://" ++ parts.authority ++ target
      else parts.scheme ++ "://" ++ parts.authority ++ "/" ++ target

private def readBody (limits : Limits) (response : Leancurl.Response) :
    Except FetchError Document :=
  let size := response.body.size
  if limits.maxBytes < size then .error (.tooLarge size)
  else if response.status < 200 || 300 ≤ response.status then .error (.status response.status)
  else match String.fromUTF8? response.body with
    | none => .error (.malformedUrl "")
    | some body => .ok { body, freshFor := freshness response.headers, size }

/-- Redirects are followed here rather than by libcurl, which is what AUTH-6.13 requires: a
redirect followed inside the transport is a host this policy never saw. The budget is the
recursion's measure, so the walk terminates whatever a provider answers with. -/
private def follow {m : Type → Type} [Monad m] (http : Http m) (limits : Limits) :
    Nat → String → m (Except FetchError Document)
  | 0, _ => pure (.error .tooManyRedirects)
  | budget + 1, url => do
    match permitted url with
    | .error e => pure (.error e)
    | .ok _ =>
      match ← http.send
          { url, method := .get, followRedirects := false, timeoutMs := some limits.timeoutMs } with
      | .error e => pure (.error (.transport e.code e.message))
      | .ok response =>
        if isRedirect response.status then
          match header? response.headers "location" with
          | none => pure (.error .redirectWithoutLocation)
          | some target => follow http limits budget (resolveLocation url target)
        else pure (readBody limits response)

/-- A document, fetched under the rules of AUTH-6.13. -/
def document {m : Type → Type} [Monad m] (http : Http m) (limits : Limits := {}) (url : String) :
    m (Except FetchError Document) :=
  follow http limits (limits.maxRedirects + 1) url

/-- A form post, for a token endpoint. No redirect is followed: an endpoint that answers a token
request with a redirect is not one this library has anything to say to, and following it would
put the request body somewhere the caller did not name. -/
def form {m : Type → Type} [Monad m] (http : Http m) (limits : Limits := {}) (url : String)
    (headers : Leancurl.Headers) (body : String) : m (Except FetchError Document) := do
  match permitted url with
  | .error e => pure (.error e)
  | .ok _ =>
    match ← http.send
        { url
          method := .post
          headers := ("Content-Type", "application/x-www-form-urlencoded") :: headers
          body := some body.toUTF8
          followRedirects := false
          timeoutMs := some limits.timeoutMs } with
    | .error e => pure (.error (.transport e.code e.message))
    | .ok response => pure (readBody limits response)

end Authentication.Fetch
