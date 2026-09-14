/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import AuthenticationFetch

/-!
The fetch policy of AUTH-6.13.

The refusals are the point. A URL reaches this code because a stranger put it somewhere, so the
checks worth running are the ones that keep a request from leaving at all, and the one that keeps
a redirect from reaching a host the checks never saw.
-/

namespace Tests.Fetch
open Authentication Authentication.Fetch

private def refusedAs {α : Type} (expected : FetchError) (result : Except FetchError α) : Bool :=
  match result with
  | .error actual => actual == expected
  | .ok _ => false

private def allowed {α : Type} (result : Except FetchError α) : Bool :=
  match result with
  | .ok _ => true
  | .error _ => false

/-- Nothing leaves, so the whole of this is decided before a socket is opened. -/
def permittedChecks : List (String × Bool) :=
  [ ("fetch: an https URL on a public host is permitted",
      allowed (permitted "https://accounts.example.com/.well-known/openid-configuration"))
  , ("fetch: http is refused (AUTH-6.13)",
      refusedAs (.notHttps "http://accounts.example.com/x") (permitted "http://accounts.example.com/x"))
  , ("fetch: loopback by name is refused",
      refusedAs (.privateAddress "localhost") (permitted "https://localhost/x"))
  , ("fetch: loopback by address is refused",
      refusedAs (.privateAddress "127.0.0.1") (permitted "https://127.0.0.1/x"))
  , ("fetch: a private range is refused",
      refusedAs (.privateAddress "10.1.2.3") (permitted "https://10.1.2.3/x"))
  , ("fetch: link-local metadata is refused",
      refusedAs (.privateAddress "169.254.169.254") (permitted "https://169.254.169.254/latest"))
  , ("fetch: a carrier-private range is refused",
      refusedAs (.privateAddress "172.16.0.5") (permitted "https://172.16.0.5/x"))
  , ("fetch: userinfo in the authority is refused, not read as its host",
      refusedAs (.malformedUrl "https://trusted.example@evil.test/x")
        (permitted "https://trusted.example@evil.test/x"))
  , ("fetch: a URL with no authority is refused",
      refusedAs (.malformedUrl "not-a-url") (permitted "not-a-url")) ]

private def response (status : UInt32) (headers : Leancurl.Headers) (body : String) :
    Leancurl.Response :=
  { status, headers, body := body.toUTF8 }

/-- Answers from a script, and records every URL it was asked for, so a check can say where the
request went as well as what came back. -/
private def scripted (script : List Leancurl.Response) (seen : IO.Ref (List String)) : Http IO where
  send request := do
    seen.modify (· ++ [request.url])
    let asked := (← seen.get).length
    pure (.ok (script[asked - 1]?.getD (response 500 [] "")))

def checks : IO (List (String × Bool)) := do
  let seen ← IO.mkRef []
  let plain ← document (scripted [response 200 [("Cache-Control", "max-age=3600")] "{}"] seen) {}
    "https://accounts.example.com/doc"

  let redirectSeen ← IO.mkRef []
  let redirected ← document
    (scripted
      [ response 302 [("Location", "https://elsewhere.example.com/moved")] ""
      , response 200 [] "{\"ok\":true}" ] redirectSeen)
    {} "https://accounts.example.com/doc"
  let redirectUrls ← redirectSeen.get

  -- The redirect is what the policy would otherwise never see: libcurl would have followed it
  -- inside the transport, and the host it landed on would never have been checked.
  let evilSeen ← IO.mkRef []
  let toPrivate ← document
    (scripted [response 302 [("Location", "https://169.254.169.254/latest")] ""] evilSeen)
    {} "https://accounts.example.com/doc"
  let evilUrls ← evilSeen.get

  let loopSeen ← IO.mkRef []
  let looping ← document
    (scripted (List.replicate 6 (response 302 [("Location", "https://a.example.com/next")] ""))
      loopSeen) {} "https://a.example.com/start"

  let bigSeen ← IO.mkRef []
  let tooBig ← document (scripted [response 200 [] (String.ofList (List.replicate 40 'x'))] bigSeen)
    { maxBytes := 8 } "https://accounts.example.com/doc"

  let failSeen ← IO.mkRef []
  let notFound ← document (scripted [response 404 [] "gone"] failSeen)
    {} "https://accounts.example.com/doc"

  let postSeen ← IO.mkRef []
  let posted ← form (scripted [response 200 [] "{\"access_token\":\"t\"}"] postSeen) {}
    "https://accounts.example.com/token" [] "grant_type=authorization_code"

  pure
    [ ("fetch: a document comes back with its body",
        (plain.toOption.map (·.body)) == some "{}")
    , ("fetch: max-age is read off the response (AUTH-6.4)",
        (plain.toOption.bind (·.freshFor)) == some ⟨3600⟩)
    , ("fetch: a redirect to a permitted host is followed",
        (redirected.toOption.map (·.body)) == some "{\"ok\":true}")
    , ("fetch: following it actually went to the named host",
        redirectUrls == ["https://accounts.example.com/doc", "https://elsewhere.example.com/moved"])
    , ("fetch: a redirect to a private address is refused (AUTH-6.13)",
        refusedAs (.privateAddress "169.254.169.254") toPrivate)
    , ("fetch: and no request was made to it",
        evilUrls == ["https://accounts.example.com/doc"])
    , ("fetch: a redirect chain is bounded", refusedAs .tooManyRedirects looping)
    , ("fetch: a body past the limit is refused", refusedAs (.tooLarge 40) tooBig)
    , ("fetch: a failing status is reported as one", refusedAs (.status 404) notFound)
    , ("fetch: a form post returns its body",
        (posted.toOption.map (·.body)) == some "{\"access_token\":\"t\"}") ]

end Tests.Fetch
