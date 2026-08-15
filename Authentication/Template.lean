/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Authentication.Digest
import Authentication.Email
import Authentication.Time

/-!
Email bodies (AUTH-10.7).

A template is a function, so a client overrides one by supplying its own rather than by filling
in a string with holes in it. What it is given carries nothing the requester typed, which is how
AUTH-5.2.12 is kept here as well as at the port: there is nowhere to put it.

The text part is not optional, and the HTML part escapes everything it interpolates.
-/

namespace Authentication

/-- Recorded against the attempt and stated in the mail, so the recipient can tell whether the
request was theirs (AUTH-5.2.12). -/
structure RequestContext where
  ip : Option String := none
  userAgent : Option String := none
  approximateLocation : Option String := none
  deriving DecidableEq, Repr, Inhabited

/-- The link is a `String` rather than a `Url` because a template is below the configuration
that knows how to build one. -/
structure SignInDetails where
  tenantName : String
  recipient : EmailAddress
  magicLink : String
  emailedCode : Option String
  requester : RequestContext
  requestedAt : Timestamp
  deriving DecidableEq, Repr, Inhabited

/-- The text part is not an `Option`: a message with no plain text part is not one this library
will send (AUTH-10.7). -/
structure RenderedEmail where
  subject : String
  textBody : String
  htmlBody : Option String := none
  deriving DecidableEq, Repr, Inhabited

private def escapeChar : Char → List Char
  | '&' => ['&', 'a', 'm', 'p', ';']
  | '<' => ['&', 'l', 't', ';']
  | '>' => ['&', 'g', 't', ';']
  | '"' => ['&', 'q', 'u', 'o', 't', ';']
  | '\'' => ['&', '#', '3', '9', ';']
  | c => [c]

def escapeHtml (s : String) : String := String.ofList (s.toList.flatMap escapeChar)

/-- The characters an interpolated value would need to open a tag or close an attribute. -/
def markupChars : List Char := ['<', '>', '"', '\'']

theorem not_mem_escapeChar {c : Char} (h : c ∈ markupChars) (b : Char) :
    c ∉ escapeChar b := by
  simp only [markupChars, List.mem_cons, List.not_mem_nil, or_false] at h
  fun_cases escapeChar b <;>
    obtain rfl | rfl | rfl | rfl := h <;>
      simp_all [Ne.symm]

/--
No escaped value can open a tag or close an attribute, whatever it contains. This is what makes
one HTML template safe for every value a template interpolates through `escapeHtml`, rather than
safe for the values that were tried.
-/
theorem escapeHtml_removes_markup {c : Char} (h : c ∈ markupChars) (s : String) :
    c ∉ (escapeHtml s).toList := by
  simp only [escapeHtml, String.toList_ofList, List.mem_flatMap]
  rintro ⟨b, -, hb⟩
  exact not_mem_escapeChar h b hb

private def requesterLine (requester : RequestContext) : String :=
  match requester.ip, requester.approximateLocation with
  | some ip, some place => s!"from {ip}, near {place}"
  | some ip, none => s!"from {ip}"
  | none, some place => s!"from near {place}"
  | none, none => "from an unrecorded address"

private def standardText (message : SignInDetails) : String :=
  let code :=
    match message.emailedCode with
    | some value => s!"\n\nOr type this code instead: {value}"
    | none => ""
  s!"Someone asked to sign in to {message.tenantName} as {message.recipient.render}, " ++
  s!"{requesterLine message.requester}, at {message.requestedAt.epochSeconds} (epoch seconds).\n\n" ++
  s!"To continue, open:\n{message.magicLink}{code}\n\n" ++
  "If this was not you, you can ignore this message. Nobody can sign in without opening " ++
  "the link above."

private def standardHtml (message : SignInDetails) : String :=
  let e := escapeHtml
  let code :=
    match message.emailedCode with
    | some value => s!"<p>Or type this code instead: <strong>{e value}</strong></p>"
    | none => ""
  s!"<p>Someone asked to sign in to {e message.tenantName} as " ++
  s!"{e message.recipient.render}, {e (requesterLine message.requester)}, at " ++
  s!"{message.requestedAt.epochSeconds} (epoch seconds).</p>" ++
  s!"<p><a href=\"{e message.magicLink}\">Sign in to {e message.tenantName}</a></p>" ++
  code ++
  "<p>If this was not you, you can ignore this message. Nobody can sign in without opening " ++
  "the link above.</p>"

structure EmailTemplates where
  signIn : SignInDetails → RenderedEmail

namespace EmailTemplates

def standard : EmailTemplates where
  signIn message :=
    { subject := s!"Sign in to {message.tenantName}"
      textBody := standardText message
      htmlBody := some (standardHtml message) }

instance : Inhabited EmailTemplates := ⟨standard⟩

end EmailTemplates

end Authentication
