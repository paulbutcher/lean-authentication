/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Authentication.Config

/-!
AUTH-4.3.5. A doubled slash is worth theorems rather than examples because of where it
surfaces: the deploy succeeds, the mail arrives, and the link answers 404 from an inbox, where
nothing can be corrected.
-/

namespace Tests.Config
open Authentication

/--
Trimming leaves no trailing slash behind, however many there were. This is the fact the two
halves of AUTH-4.3.5 below both rest on: a URL built from an origin ending in a slash meets the
tenant path's own leading slash and answers 404 from an inbox, where nothing can be corrected.

`origin` is an arbitrary string, so nothing is assumed about how many trailing slashes it
carries or whether it carries any. `getLast?` gives the last character of the trimmed result, or
`none` when it is empty, and the conclusion is that this is not `some '/'`. The empty result is
therefore admitted, and deliberately: an origin of nothing but slashes trims to nothing, which
`trim_slashes_only` states outright.
-/
theorem trim_leaves_no_trailing_slash (origin : String) :
    (BaseUrl.trimTrailingSlashes origin).toList.getLast? ≠ some '/' := by
  simp only [BaseUrl.trimTrailingSlashes, String.toList_ofList, List.getLast?_reverse]
  intro h
  have := List.head?_dropWhile_not (· == '/') origin.toList.reverse
  rw [h] at this
  simp at this

/--
The half of AUTH-4.3.5 that holds where a `BaseUrl` is made, so a client that normalises on the
way in gets a value it can store and read back without the doubled slash ever existing.

`BaseUrl.ofString` is the normalising constructor and `.origin` is the string it keeps.
`getLast?` returns the final character, or `none` for the empty string, and the conclusion says
it is not `some '/'`. The empty case satisfies this rather than evading it: `none` is not `some`,
and an origin trimmed to nothing is the subject of `trim_slashes_only` below. `origin` is
arbitrary, so any number of trailing slashes is covered.
-/
theorem ofString_leaves_no_trailing_slash (origin : String) :
    (BaseUrl.ofString origin).origin.toList.getLast? ≠ some '/' :=
  trim_leaves_no_trailing_slash origin

/--
The half that holds where a `BaseUrl` is used, which is the half a literal `⟨origin⟩` depends on.
`BaseUrl` is an ordinary structure, so a client may write one directly and never reach
`ofString`; this says the resulting URL is the same either way.

`base` is any `BaseUrl` and `⟨base.origin ++ "/"⟩` is the same one with a slash appended, which
is exactly the mistake in question. The conclusion equates the two URLs `BaseUrl.url` builds
from them, for any tenant and any path, so the extra slash cannot reach the output. One
appended slash is enough to cover any number of them, because `base` itself is unconstrained and
may already end in as many as one likes.
-/
theorem url_ignores_trailing_slash (base : BaseUrl) (tenant : TenantId) (path : String) :
    BaseUrl.url ⟨base.origin ++ "/"⟩ tenant path = BaseUrl.url base tenant path := by
  simp [BaseUrl.url, BaseUrl.trimTrailingSlashes, String.toList_append]

/--
Only the end is touched: an origin carrying a path prefix keeps every character of it. Without
this, the other theorems here would be satisfied by a trim that discarded far more than the
trailing slashes, and a deployment mounted under a path would break.

`h` says the origin does not already end in a slash, `getLast?` answering `some '/'` being what
it would mean if it did. The conclusion is that trimming returns the origin unchanged, character
for character, rather than merely returning something with the same tail. `origin` is otherwise
arbitrary, so slashes inside it, including doubled ones, are kept.
-/
theorem trim_keeps_everything_else (origin : String) (h : origin.toList.getLast? ≠ some '/') :
    BaseUrl.trimTrailingSlashes origin = origin := by
  rw [BaseUrl.trimTrailingSlashes, List.dropWhile_beq_eq_self_of_head?_ne (by simpa using h),
    List.reverse_reverse, String.ofList_toList]

/--
An origin of nothing but slashes trims away entirely rather than to a slash, so what it builds
has no host and fails where it is read. The alternative worth ruling out is a trim that stops
one character short and yields a URL relative to whatever host the browser was already on.

`n` ranges over every natural number, so the empty origin, a single slash, and any longer run
are all covered. `String.ofList (List.replicate n '/')` is the origin made of exactly `n`
slashes, and the conclusion is that trimming it gives the empty string exactly. Emptiness is the
point: the failure it produces is one a client sees on the first request, not one that reaches a
mailbox.
-/
theorem trim_slashes_only (n : Nat) :
    BaseUrl.trimTrailingSlashes (String.ofList (List.replicate n '/')) = "" := by
  simp [BaseUrl.trimTrailingSlashes]

/-- The value a client is most likely to copy: AWS publishes a Lambda function URL with a
trailing slash, and other platforms publish an origin the same way. -/
example : (BaseUrl.url ⟨"https://app.example.com/"⟩ ⟨"acme"⟩ "/signin/link").value
    = "https://app.example.com/t/acme/signin/link" := by decide

/-!
Cookie `Secure` (AUTH-9.2), derived from the origin's scheme rather than fixed, so that a
cookie a browser would discard over `http` is not issued in the first place.
-/

/--
Two builders that could disagree is the failure the derivation introduces: a session cookie a
browser stores alongside an attempt cookie it drops leaves sign-in half-working, and only in the
browser strictest about it.

`CookieSpec.forAttempt` and `CookieSpec.forSession` are the two places a cookie is built, and
`.secure` is the flag each derives from the origin's scheme. The two are applied to the same
`base` and to otherwise unrelated arguments: different values, different expiries, and a path
that only the session cookie takes. The conclusion equates the flags, so nothing but the origin
can move either, which is what stops the pair drifting apart as the builders are edited. It says
nothing about which value the flag takes; that is what `secureCookies` and the examples below
fix.
-/
theorem attempt_and_session_agree_on_secure (base : BaseUrl) (tenant : TenantId)
    (path attemptValue sessionValue : String) (attemptExpiry sessionExpiry : Timestamp) :
    (CookieSpec.forAttempt base tenant attemptValue attemptExpiry).secure
      = (CookieSpec.forSession base path sessionValue sessionExpiry).secure :=
  rfl

/-- The deployed case, which has to come out exactly as it did when the flag was a constant. -/
example : (BaseUrl.ofString "https://app.example.com/").secureCookies := by decide

/-- Local development, where `Secure` is what stops Safari storing the cookie at all. -/
example : (BaseUrl.ofString "http://localhost:8080").secureCookies = false := by decide

/-- A scheme is case-insensitive, and an origin read from an environment need not be lowercase. -/
example : (BaseUrl.ofString "HTTP://localhost").secureCookies = false := by decide

end Tests.Config
