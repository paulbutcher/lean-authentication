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

theorem trim_leaves_no_trailing_slash (origin : String) :
    (BaseUrl.trimTrailingSlashes origin).toList.getLast? ≠ some '/' := by
  simp only [BaseUrl.trimTrailingSlashes, String.toList_ofList, List.getLast?_reverse]
  intro h
  have := List.head?_dropWhile_not (· == '/') origin.toList.reverse
  rw [h] at this
  simp at this

/-- The half of AUTH-4.3.5 that holds where a `BaseUrl` is made. -/
theorem ofString_leaves_no_trailing_slash (origin : String) :
    (BaseUrl.ofString origin).origin.toList.getLast? ≠ some '/' :=
  trim_leaves_no_trailing_slash origin

/-- The half that holds where one is used, which is the half a literal `⟨origin⟩` depends on. -/
theorem url_ignores_trailing_slash (base : BaseUrl) (tenant : TenantId) (path : String) :
    BaseUrl.url ⟨base.origin ++ "/"⟩ tenant path = BaseUrl.url base tenant path := by
  simp [BaseUrl.url, BaseUrl.trimTrailingSlashes, String.toList_append]

/-- Only the end is touched: an origin carrying a path prefix keeps every character of it. -/
theorem trim_keeps_everything_else (origin : String) (h : origin.toList.getLast? ≠ some '/') :
    BaseUrl.trimTrailingSlashes origin = origin := by
  rw [BaseUrl.trimTrailingSlashes, List.dropWhile_beq_eq_self_of_head?_ne (by simpa using h),
    List.reverse_reverse, String.ofList_toList]

/-- An origin of nothing but slashes trims away entirely rather than to a slash, so what it
builds has no host and fails where it is read. -/
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

/-- Two builders that could disagree is the failure the derivation introduces: a session cookie
a browser stores alongside an attempt cookie it drops leaves sign-in half-working, and only in
the browser strictest about it. -/
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
