/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Authentication

/-!
Consent history (§4.6).

The store keeps every entry and the current answer is a fold over them, so the two properties
worth proving are that the fold reads the last word and that subjects do not interfere.
-/

namespace Tests.Consent
open Authentication

variable {tenant : TenantId}

/-- The last entry about a subject decides where it stands, whichever way it went. An earlier
grant cannot outvote a later withdrawal (AUTH-4.6.4). -/
theorem granted_last (history : List (ConsentEntry tenant)) (entry : ConsentEntry tenant) :
    Consent.granted (history ++ [entry]) entry.subject = (entry.act == .granted) := by
  simp [Consent.granted, Consent.latest, List.filter_append]

/-- An answer about one subject says nothing about another. -/
theorem granted_other (history : List (ConsentEntry tenant)) (entry : ConsentEntry tenant)
    (subject : ConsentSubject) (h : entry.subject ≠ subject) :
    Consent.granted (history ++ [entry]) subject = Consent.granted history subject := by
  simp [Consent.granted, Consent.latest, List.filter_append, h]

/-- Silence is not consent. -/
theorem granted_empty (subject : ConsentSubject) :
    Consent.granted ([] : List (ConsentEntry tenant)) subject = false := by
  simp [Consent.granted, Consent.latest]

end Tests.Consent
