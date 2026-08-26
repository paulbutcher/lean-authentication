/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Authentication.Consent
public import AuthenticationOAuth.Client
public import AuthenticationOAuth.Scope

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
