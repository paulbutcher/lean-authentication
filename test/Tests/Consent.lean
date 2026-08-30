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

/--
The last entry about a subject decides where it stands, whichever way it went. An earlier grant
cannot outvote a later withdrawal (AUTH-4.6.4), which is what makes an append-only history safe
to keep: nothing has to be deleted for a withdrawal to take effect.

`Consent.granted` folds a history, oldest first, into the current answer for one subject, and
`history ++ [entry]` puts `entry` last. The conclusion equates that answer with `entry.act ==
.granted`, the single entry's own verdict, so whatever `history` contains is overruled. Both
directions are covered because `entry.act` is unconstrained: a trailing grant yields `true` and a
trailing withdrawal `false`, regardless of how many entries of the other kind precede it.
-/
theorem granted_last (history : List (ConsentEntry tenant)) (entry : ConsentEntry tenant) :
    Consent.granted (history ++ [entry]) entry.subject = (entry.act == .granted) := by
  simp [Consent.granted, Consent.latest, List.filter_append]

/--
An answer about one subject says nothing about another. Subjects are per client and per
resource, so without this a grant to one client could be read as a grant to every client whose
entries share the history.

`history ++ [entry]` appends one entry to an arbitrary history, and `h` says that entry is about
a different subject from the one being read. The conclusion equates the answer before and after
the append, so the new entry moves nothing: not a grant into a refusal, and not a refusal into a
grant. `entry.act` is unconstrained, so a withdrawal about one subject cannot withdraw another's
grant either.
-/
theorem granted_other (history : List (ConsentEntry tenant)) (entry : ConsentEntry tenant)
    (subject : ConsentSubject) (h : entry.subject ≠ subject) :
    Consent.granted (history ++ [entry]) subject = Consent.granted history subject := by
  simp [Consent.granted, Consent.latest, List.filter_append, h]

/--
Silence is not consent. A subject nobody has been asked about stands refused, so a store that
has lost its history, or one being read before anything was written, cannot be mistaken for one
recording a grant.

`Consent.granted` is the fold that reads a history for one subject, and here the history is
empty and the subject arbitrary. The conclusion is `false` rather than an `Option`, so there is
no absent value for a caller to default the wrong way. This is the `none` branch of `granted`,
which the two theorems above leave open by only ever appending to a history.
-/
theorem granted_empty (subject : ConsentSubject) :
    Consent.granted ([] : List (ConsentEntry tenant)) subject = false := by
  simp [Consent.granted, Consent.latest]

end Tests.Consent
