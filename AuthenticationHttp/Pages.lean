/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Authentication
import Html

/-!
The pages the sign-in routes render.

Held as a record of functions rather than written into the handlers, for the reason AUTH-10.7
gives about mail: a client supplies its own rather than filling in holes in one this library
dictates. The defaults are unstyled and semantic, so a client that overrides nothing gets
something that works and a client that overrides everything is not fighting a stylesheet.

Nothing here decides anything. What is said when a sign-in cannot proceed was already decided by
the response policy (§14.2); these functions render the decision.
-/

namespace Authentication.Http

open Html

/-- What a page is given. `action` and `token` are empty on a page with no form. -/
structure PageContext where
  tenantName : String
  action : String := ""
  /-- Bound to the attempt cookie, so a form posted from another origin carries the wrong one
  (AUTH-14.1.4). -/
  token : Option String := none
  /-- Where the person asked to land, carried forward so that the browser being signed in is the
  one that says where it is going. It is validated where it is used, not here (AUTH-9.8). -/
  returnTo : Option String := none
  /-- Set only when the tenant puts a code in the mail body (AUTH-5.4.1). It is a second action
  rather than a second meaning for the first, because the two codes are distinct credentials and
  trying one against the other would spend two of the five entries they share (AUTH-5.4.2). -/
  emailedCodeAction : Option String := none

structure Pages where
  signIn : PageContext → String
  /-- What the person is told after asking for a link, and the field the code is typed into. The
  two are one page because the person types the code into the browser they asked from. -/
  sent : PageContext → SignInMessage → String
  confirm : PageContext → String
  /-- The cross-device page: it shows the code rather than accepting one, because the browser
  that opened the link is not the browser that will be signed in (AUTH-5.2.2). -/
  code : PageContext → (code : String) → String
  codeRejected : PageContext → (remaining : Nat) → String
  refused : PageContext → SignInRefusal → String
  unknown : String

namespace Pages

private def page (title : String) (children : List (Node .flow)) : String :=
  Html.document (lang := "en")
    [ Html.head
        [ Html.meta_ [("charset", "utf-8")],
          Html.meta_ [("name", "viewport"), ("content", "width=device-width, initial-scale=1")],
          Html.title title ],
      Html.body [Html.main children] ]

/-- Carried in the form rather than in a header, because the magic link's landing page is reached
by a top-level navigation and has no script to add one (AUTH-14.1.4). -/
private def hidden (name : String) (value : Option String) : List (Node .flow) :=
  match value with
  | none => []
  | some value => [Html.input { type := "hidden", name, value }]

private def carried (context : PageContext) : List (Node .flow) :=
  hidden "token" context.token ++ hidden "returnTo" context.returnTo

private def messageText : SignInMessage → String
  | .checkYourMail => "If that address can sign in, a link is on its way to it."
  | .addressNotRecognised => "That address does not have an account here."
  | .invitationRequired => "This organisation is invitation only."
  | .domainNotAllowed => "This organisation does not accept that address's domain."
  | .tryAgainLater => "Too many attempts. Try again later."
  | .addressMalformed => "That does not look like an email address."
  | .accountUnavailable => "That account is closed."

private def refusalText : SignInRefusal → String
  | .signup .notInvited => "This organisation is invitation only, and you were not invited."
  | .signup .domainNotAllowed => "This organisation does not accept that address's domain."
  | .accountDeactivated => "That account is closed."

private def oneCodeForm (context : PageContext) (action label id : String) : Node .flow :=
  Html.form
    ([ Html.p [ Html.label [Node.text label] { for_ := id } ],
       Html.p
         [ Html.input
             { type := "text", name := "code", id, required := true }
             [("autocomplete", "one-time-code"), ("autocapitalize", "off"),
              ("spellcheck", "false")] ] ]
      ++ carried context
      ++ [Html.p [Html.button [Node.text "Sign in"]]])
    { method := "post", action }

private def codeForm (context : PageContext) : List (Node .flow) :=
  oneCodeForm context context.action "Verification code" "code"
    :: match context.emailedCodeAction with
      | none => []
      | some action => [oneCodeForm context action "Code from the email" "emailed-code"]

def standard : Pages where
  signIn context :=
    page s!"Sign in to {context.tenantName}"
      [ Html.h1 [Node.text s!"Sign in to {context.tenantName}"],
        Html.form
          ([ Html.p [Html.label [Node.text "Email address"] { for_ := "email" }],
             Html.p
               [ Html.input
                   { type := "email", name := "email", id := "email", required := true }
                   [("autocomplete", "email"), ("autocapitalize", "off"),
                    ("spellcheck", "false")] ] ]
            ++ hidden "returnTo" context.returnTo
            ++ [Html.p [Html.button [Node.text "Send me a link"]]])
          { method := "post", action := context.action } ]
  sent context message :=
    page s!"Sign in to {context.tenantName}"
      ([ Html.h1 [Node.text "Check your mail"],
        Html.p [Node.text (messageText message)],
        Html.p
          [ Node.text
              "If you opened the link on another device, type the code it showed you here." ] ]
      ++ codeForm context)
  confirm context :=
    page s!"Sign in to {context.tenantName}"
      [ Html.h1 [Node.text s!"Sign in to {context.tenantName}"],
        Html.p [Node.text "You opened this link in the browser you asked from."],
        Html.form
          (carried context ++ [Html.p [Html.button [Node.text "Sign in"]]])
          { method := "post", action := context.action } ]
  code context shown :=
    page s!"Sign in to {context.tenantName}"
      [ Html.h1 [Node.text "Your verification code"],
        Html.p
          [ Node.text "Type this into the browser you asked to sign in from. ",
            Node.text "It will not sign you in on this device." ],
        Html.p [Html.strong [Html.code [Node.text shown]]] ]
  codeRejected context remaining :=
    page s!"Sign in to {context.tenantName}"
      ([ Html.h1 [Node.text "That code is not right"],
        Html.p
          [ Node.text
              (if remaining == 0 then "No attempts remain. Ask for a new link."
                else s!"{remaining} attempts remain.") ] ]
      ++ codeForm context)
  refused context reason :=
    page s!"Sign in to {context.tenantName}"
      [ Html.h1 [Node.text "You cannot sign in"],
        Html.p [Node.text (refusalText reason)] ]
  unknown := page "Not found" [Html.h1 [Node.text "Not found"]]

instance : Inhabited Pages := ⟨standard⟩

end Pages

end Authentication.Http
