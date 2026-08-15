/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Authentication

/-!
Email templates (AUTH-10.7).

That escaping cannot be defeated is a theorem in `Authentication/Template.lean`. What is left
here is what a theorem does not constrain: that the standard template renders both parts, that
it puts the values where they belong, and that a tenant's override is what gets used.
-/

namespace Tests.Template
open Authentication

private def address (raw : String) : EmailAddress := (EmailAddress.parse raw).toOption.getD default

private def details : SignInDetails :=
  { tenantName := "Acme"
    recipient := address "person@example.com"
    magicLink := "https://auth.example.com/t/acme/open?attempt=a1&token=t1"
    emailedCode := some "ABCD-EFGH"
    requester := { ip := some "198.51.100.7", approximateLocation := some "Leeds" }
    requestedAt := ⟨1700000000⟩ }

/-- A display name is operator-controlled, but a template that escapes only what an attacker
supplies is a template someone has to keep reasoning about. -/
private def hostile : SignInDetails :=
  { details with tenantName := "<script>alert('x')</script>" }

private def occurs (needle haystack : String) : Bool := (haystack.splitOn needle).length > 1

def checks : List (String × Bool) :=
  let rendered := EmailTemplates.standard.signIn details
  let attacked := EmailTemplates.standard.signIn hostile
  let overridden :=
    { EmailTemplates.standard with
      signIn := fun d => { subject := s!"Hello from {d.tenantName}", textBody := "brief" } }
      |>.signIn details
  [ ("template: the subject names the tenant", rendered.subject == "Sign in to Acme"),
    ("template: the text part carries the link and the code",
      occurs details.magicLink rendered.textBody && occurs "ABCD-EFGH" rendered.textBody),
    ("template: the text part states where the request came from",
      occurs "198.51.100.7" rendered.textBody && occurs "Leeds" rendered.textBody),
    ("template: an HTML part is offered and links to the same URL",
      match rendered.htmlBody with
      | some html => occurs "href=" html && occurs "auth.example.com" html
      | none => false),
    ("template: the HTML part escapes the ampersand in the link, and the text part does not",
      match rendered.htmlBody with
      | some html => occurs "attempt=a1&amp;token=t1" html && occurs "attempt=a1&token=t1" rendered.textBody
      | none => false),
    ("template: a value containing markup cannot introduce a tag",
      match attacked.htmlBody with
      | some html => !occurs "<script>" html && occurs "&lt;script&gt;" html
      | none => false),
    ("template: an override replaces the standard rendering",
      overridden.subject == "Hello from Acme" && overridden.htmlBody.isNone) ]

end Tests.Template
