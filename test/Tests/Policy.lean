/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Authentication.Policy
import Tests.Email

namespace Tests.Policy
open Authentication

/--
AUTH-16.1 and AUTH-7.3.1: matching is a relation between label lists, so a domain is accepted
only when the allowed domain's labels are a whole suffix of its own. A text suffix that falls
inside a label, which is the failure that turns a domain restriction into no restriction, is not
expressible as an outcome of this function.

`Domain.allows allowed candidate true` is the matcher with subdomains permitted, and `<:+` is
suffix on lists, which compares whole labels and cannot end part-way through one. The
biconditional is what makes this exhaustive rather than a sample: acceptance implies the suffix
relation, so nothing else is ever admitted, and the suffix relation implies acceptance, so a
genuine subdomain is not turned away. `allowed` and `candidate` are arbitrary domains, the empty
label list included; what that case admits is everything, and it is a domain the parser never
produces.
-/
theorem allows_iff_label_suffix (allowed candidate : Domain) :
    allowed.allows candidate true = true ↔ allowed.labels <:+ candidate.labels := by
  simp [Domain.allows]

/--
Without subdomains the relation is equality of label lists, so a restriction that named a domain
admits that domain and nothing under it. This is the other half of the switch, and it is worth
stating because a match that fell back to suffix behaviour would silently admit every subdomain
of an allowlisted domain.

`Domain.allows allowed candidate false` is the matcher with subdomains turned off. The
biconditional gives both directions: the label lists are equal exactly when the domain is
accepted, so nothing is accepted that is not the domain itself, and the domain itself is not
turned away. Equality is between label lists rather than rendered text, which is what makes the
statement independent of how a domain was spelled.
-/
theorem allows_exactly_iff_equal (allowed candidate : Domain) :
    allowed.allows candidate false = true ↔ allowed.labels = candidate.labels := by
  simp [Domain.allows]

/--
The same statement about the text rather than the labels, which is the form AUTH-7.3.1 is
written in: an accepted domain either is the allowed domain or ends with it after a separator.
There is no accepted domain whose text merely ends with the allowed text, which is the case that
would let `evilexample.com` past a restriction to `example.com`.

`h` says the candidate was accepted with subdomains allowed, and `hne` says the allowed domain
has at least one label. The disjunction is over the rendered text: either the two render alike,
which is the exact match, or the candidate's text is something followed by a dot and then the
allowed text, which is the subdomain case. The dot is written explicitly, so a candidate whose
text ends with the allowed text without one is in neither branch and therefore was not accepted.
`hne` is what rules out the empty allowed domain, for which every domain would trivially end
with nothing and the statement would say less than it appears to.
-/
theorem allows_implies_separated_suffix (allowed candidate : Domain) (hne : allowed.labels ≠ [])
    (h : allowed.allows candidate true = true) :
    candidate.render = allowed.render ∨
      ∃ before, candidate.render.toList = before ++ '.' :: allowed.render.toList := by
  obtain ⟨before, hbefore⟩ := (allows_iff_label_suffix allowed candidate).mp h
  match before, hbefore with
  | [], hbefore => exact Or.inl (by simp [Domain.render, ← hbefore])
  | b :: bs, hbefore =>
    refine Or.inr ⟨Authentication.joinWithDot ((b :: bs).map String.toList), ?_⟩
    have hmapped : allowed.labels.map String.toList ≠ [] := by simpa using hne
    have hbs : (b :: bs).map String.toList ≠ [] := by simp
    simp only [Domain.render, ← hbefore, List.map_append, String.toList_ofList,
      Tests.Email.joinWithDot_append _ _ hbs hmapped]

/-- The case the requirement calls out by name. -/
example : (Domain.mk ["example", "com"]).allows ⟨["evilexample", "com"]⟩ true = false := by decide

example : (Domain.mk ["example", "com"]).allows ⟨["mail", "example", "com"]⟩ true = true := by
  decide

/-- Without `includeSubdomains`, a subdomain is not a match either (AUTH-7.3.2). -/
example : (Domain.mk ["example", "com"]).allows ⟨["mail", "example", "com"]⟩ false = false := by
  decide

/-- Two spellings differing only in case are the same parsed domain, so matching cannot
distinguish them (AUTH-7.3.3, AUTH-4.5.2). -/
example : Domain.parse "Example.COM" = .ok ⟨["example", "com"]⟩ := by rfl

example : Domain.parse "example.com" = .ok ⟨["example", "com"]⟩ := by rfl

/-- An invitation overrides an allowlist only when the tenant allows it (AUTH-7.5). -/
example :
    SignupPolicy.evaluate (.domainAllowlist [⟨["example", "com"]⟩] false)
      ⟨"person", ⟨["other", "com"]⟩⟩ true true = .permitted := by decide

example :
    SignupPolicy.evaluate (.domainAllowlist [⟨["example", "com"]⟩] false)
      ⟨"person", ⟨["other", "com"]⟩⟩ true false = .rejected .domainNotAllowed := by decide

example :
    SignupPolicy.evaluate .inviteOnly ⟨"person", ⟨["example", "com"]⟩⟩ false true
      = .rejected .notInvited := by decide

end Tests.Policy
