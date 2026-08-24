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

/-- One person's answer about one client and one resource. The prefix keeps it out of the way of
the subjects a host names for itself. -/
def subject (client : ClientId) (resource : ResourceIndicator) : ConsentSubject :=
  ⟨"oauth:" ++ client.value ++ "|" ++ resource.value⟩

/-- What this account has granted this client for this resource, as it stands now. Silence is
not consent, and neither is a withdrawal. -/
def granted {tenant : TenantId} (history : List (ConsentEntry tenant)) (client : ClientId)
    (resource : ResourceIndicator) : List Scope :=
  match Authentication.Consent.latest history (subject client resource) with
  | some entry => if entry.act == .granted then Scope.parse entry.version else []
  | none => []

/-- Whether anything at all stands granted, which is what decides whether a refusal is also a
withdrawal. -/
def standing {tenant : TenantId} (history : List (ConsentEntry tenant)) (client : ClientId)
    (resource : ResourceIndicator) : Bool :=
  Authentication.Consent.granted history (subject client resource)

end Authentication.OAuth.Consent
