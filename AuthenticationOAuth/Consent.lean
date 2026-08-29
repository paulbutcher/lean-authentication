/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Authentication.Consent
public import AuthenticationOAuth.Client
public import AuthenticationOAuth.Scope
public import Codec.Base64Url

/-!
A grant is a consent record (§20.14).

What an authorisation server calls a grant, this library already had: a thing a person agreed
to, the version of it they were shown, when they said so, and an append-only history in which a
withdrawal is another entry rather than an edit. Nothing about §4.6 needed changing to hold one.

The subject names the client and the resource, so one person's decisions about two clients, or
about one client and two resources, are separate answers. The version carries the scopes that
were agreed to, which is what the consent model already means by it: the client's own words,
stored verbatim and interpreted by nobody except the client that wrote them. Here that client
is this file.

The consequence worth stating: revoking a grant is `withdrawConsent`, and it is the same
operation an account holder's own privacy page already performs.

What a person was asked is also here, in the field a scope's checkbox carries. `Scope` itself
imports nothing at all, deliberately, and an encoding needs one.
-/

public section

namespace Authentication.OAuth.Consent

open Authentication

/-- What keeps these subjects out of the way of the ones a host names for itself. -/
private def marker : List Char := "oauth:".toList

private def separator : Char := '|'

/-- One person's answer about one client and one resource. -/
def subject (client : ClientId) (resource : ResourceIndicator) : ConsentSubject :=
  ⟨String.ofList (marker ++ client.value.toList ++ [separator] ++ resource.value.toList)⟩

/-- The inverse, so that a host holding a `ConsentState` can reach `revoke` without
reimplementing the encoding. `none` for a subject this file did not write.

The client is everything up to the first separator, which is the half that cannot contain one:
a dynamic identifier is base64url and a metadata document identifier is a URL, and neither
admits a bar. A resource indicator is returned whole, bars and all. -/
def parts (subject : ConsentSubject) : Option (ClientId × ResourceIndicator) :=
  let chars := subject.name.toList
  if chars.take marker.length != marker then none
  else
    let body := chars.drop marker.length
    match body.dropWhile (· != separator) with
    | [] => none
    | _ :: resource =>
      some (⟨String.ofList (body.takeWhile (· != separator))⟩, ⟨String.ofList resource⟩)

/--
The two are inverse wherever the identifier admits no separator, which is every identifier this
server will see: a dynamic one is base64url and a metadata document one is a URL, and a bar is
in neither alphabet. What it buys is that a host acting on a subject acts on the client and the
resource the decision was about rather than on a guess at them, and that the two halves of the
encoding cannot drift apart.
-/
theorem parts_inverts_subject (client : ClientId) (resource : ResourceIndicator)
    (h : ∀ c ∈ client.value.toList, c ≠ '|') :
    parts (subject client resource) = some (client, resource) := by
  have hp : ∀ a ∈ client.value.toList, (a != separator) = true := fun a ha => by
    simp [separator, h a ha]
  unfold parts subject
  simp
  rw [List.dropWhile_append_of_pos hp, List.takeWhile_append_of_pos hp]
  simp

/-- What this account has granted this client for this resource, as it stands now. Silence is
not consent, and neither is a withdrawal. -/
def granted {tenant : TenantId} (history : List (ConsentEntry tenant)) (client : ClientId)
    (resource : ResourceIndicator) : List Scope :=
  match Authentication.Consent.latest history (subject client resource) with
  | some entry => if entry.act == .granted then Scope.parse entry.version else []
  | none => []

/-- Whether what stands granted answers this request on its own, so that nobody need be asked
again.

A request that named no scopes is answered by nothing. `Scope.subset` is vacuously true of the
empty set and would report such a request as covered by a consent that does not exist; the
question here is not whether one set is contained in another but whether a decision has already
been taken, and about a request that asked for nothing none has.
-/
def covers (requested granted : List Scope) : Bool :=
  !requested.isEmpty && Scope.subset requested granted

/-- Whether anything at all stands granted, which is what decides whether a refusal is also a
withdrawal. -/
def standing {tenant : TenantId} (history : List (ConsentEntry tenant)) (client : ClientId)
    (resource : ResourceIndicator) : Bool :=
  Authentication.Consent.granted history (subject client resource)

end Authentication.OAuth.Consent

namespace Authentication.OAuth

/-- The form field a scope's checkbox carries: one name per scope, so each answer is read back
with an ordinary single-valued lookup, and encoded so that whatever the client put in the scope,
what reaches the form is `A-Za-z0-9_-`.

A scope is an opaque string the client chose, and a page that named the field after it would be
letting the client choose the field name too. A colon is enough for the browser's answer never
to be found again. -/
@[expose] def Scope.approvalField (scope : Scope) : String :=
  "approve-" ++ Codec.Base64Url.encodeString scope.value.toUTF8

/-- Which of `requested` the submitted form left ticked. `ticked` is the host's own lookup into
the body it parsed, asked once per scope under the name `approvalField` gave it, so the encoding
is written and read in one place. -/
@[expose] def Scope.approved (requested : List Scope) (ticked : String → Bool) : List Scope :=
  requested.filter fun scope => ticked scope.approvalField

/-! ### The rest of the consent form

The field the answer itself rides in, beside the one field per scope `Scope.approvalField` names.
Both are read by whatever serves the consent page and written by whatever renders it, so both are
here rather than in either. -/

namespace ConsentForm

def answerField : String := "consent"

def approveValue : String := "approve"

/-- Anything else, and anything missing, is a refusal. A page whose deny button submits a form
carrying no answer is read the way it reads to the person who pressed it, and a request that
reached the endpoint without passing through the page grants nothing. -/
def approved (submitted : Option String) : Bool := submitted == some approveValue

end ConsentForm

end Authentication.OAuth
