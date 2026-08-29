/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import AuthenticationOAuth.Consent
import Html

/-!
The pages the authorisation server's own routes render.

The same arrangement as `Pages`, for the same reason: a record of render functions with an
unstyled default, so a deployment replaces the appearance without reimplementing the routing or
the field names underneath it.

There are two of them, and there are only two because everything else this server answers is
answered to a program. The consent page is the whole of what a person is shown when the flow is
working; `refusedClient` is the whole of what they are shown when it is not, because a client
whose identity or redirect URI could not be established may be sent nothing at all.
-/

public section

namespace Authentication.OAuth.Http

open Html Authentication

/--
Everything the consent page has to show, flattened out of `ConsentPrompt` so that a page is not
handed the account identifier it has no use for.

The scopes arrive as they were asked for. Whether the deployment amended a scopeless request with
a default set was decided before this was built, so what is here is what the answer will be taken
to be about.
-/
structure ConsentContext where
  tenantName : String
  /-- Where the answer is posted: the URL this page was served from, query and all. The `POST`
  re-reads that query rather than trusting fields the page carried back. -/
  action : String
  /-- The field carrying the anti-forgery token, and the token itself. The name is the
  deployment's, since it has to match whatever `Middleware.antiForgery` was configured with where
  one is in the stack. -/
  antiForgeryField : String
  antiForgeryToken : String
  /-- What the client calls itself, which is the client's own word and nothing more. -/
  clientName : String
  /-- The host of the `client_id` URL, displayed beside the name because it is the only part of
  the pair anything vouches for (client ID metadata document draft §6.4). `none` for a client
  that registered dynamically, where nothing vouches for either. -/
  clientHost : Option String
  /-- The host the person will be sent back to, which MUST be displayed (MCP authorization
  security considerations). -/
  redirectHost : String
  /-- Whether every redirect URI this client registered is a loopback one, which SHOULD carry a
  further warning: nothing can establish who is listening on a port of this person's own
  machine. -/
  loopbackOnly : Bool
  /-- What the token will be usable at, and nowhere else. -/
  resource : ResourceIndicator
  requestedScopes : List Scope
  /-- What already stands granted to this client for this resource, so a page can show what is
  new about the request. -/
  grantedScopes : List Scope

structure OAuthPages where
  /-- Everything a person needs to decide, and the form that carries the answer back. -/
  consent : ConsentContext → String
  /-- Shown when the client, or the address it asked to be sent back to, could not be
  established. Nothing may be sent to the client in this case, so this is the only thing the
  person will see. -/
  refusedClient : (description : String) → String

namespace OAuthPages

private def page (title : String) (children : List (Node .flow)) : String :=
  Html.document (lang := "en")
    [ Html.head
        [ Html.meta_ [("charset", "utf-8")],
          Html.meta_ [("name", "viewport"), ("content", "width=device-width, initial-scale=1")],
          Html.title title ],
      Html.body [Html.main children] ]

/-- One checkbox per scope, ticked, under the field name `Scope.approvalField` fixes. Ticked
because the request is what the client asked for and unticking is how a scope is withheld; the
answer read back is what the boxes say, not what they started as. -/
private def scopeBoxes (context : ConsentContext) : List (Node .flow) :=
  context.requestedScopes.map fun scope =>
    Html.p
      [ Html.label
          [ Html.input
              { type := "checkbox", name := scope.approvalField, value := "yes", checked := true },
            Node.text " ",
            Node.text scope.value,
            Node.text
              (if context.grantedScopes.contains scope then " (already allowed)" else "") ] ]

private def clientLine (context : ConsentContext) : String :=
  let name := if context.clientName.isEmpty then "An application" else context.clientName
  match context.clientHost with
  | some host => s!"{name}, at {host}, wants access to your account."
  | none => s!"{name}, which registered itself and which no domain vouches for, wants access \
      to your account."

def standard : OAuthPages where
  consent context :=
    page s!"Allow access to {context.tenantName}"
      [ Html.h1 [Node.text "Allow access?"],
        Html.p [Node.text (clientLine context)],
        Html.p
          [ Node.text "You will be sent back to ",
            Html.strong [Node.text context.redirectHost],
            Node.text ", and it will be able to reach ",
            Html.strong [Node.text context.resource.value],
            Node.text " as you." ],
        Html.p
          (if context.loopbackOnly then
            [ Node.text
                "This application says it is running on this computer. Nothing can check that, \
                 so allow it only if you started it yourself." ]
          else []),
        Html.form
          [ Html.input
              { type := "hidden", name := context.antiForgeryField,
                value := context.antiForgeryToken },
            Html.fieldset
              (Html.legend [Node.text "What it is asking for"]
                :: (if context.requestedScopes.isEmpty then
                      [Html.p [Node.text "Nothing this server can grant."]]
                    else scopeBoxes context)),
            Html.p
              [ Html.button [Node.text "Allow"]
                  { name := ConsentForm.answerField, value := ConsentForm.approveValue },
                Node.text " ",
                Html.button [Node.text "Deny"]
                  { name := ConsentForm.answerField, value := "deny" } ] ]
          { method := "post", action := context.action } ]
  refusedClient description :=
    page "That application cannot be sent anywhere"
      [ Html.h1 [Node.text "That application cannot be sent anywhere"],
        Html.p
          [ Node.text
              "Nothing was sent back to it, because there is no address this server has \
               established as its own." ],
        Html.p [Node.text description] ]

instance : Inhabited OAuthPages := ⟨standard⟩

end OAuthPages

end Authentication.OAuth.Http
