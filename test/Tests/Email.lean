/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Authentication.Email

/-!
Parsing and normalisation theorems (AUTH-16.1).
-/

namespace Tests.Email
open Authentication

private theorem splitOnDot_ne_nil (cs : List Char) : splitOnDot cs ≠ [] := by
  induction cs using splitOnDot.induct with
  | case1 => simp [splitOnDot]
  | case2 rest _ => simp [splitOnDot]
  | case3 c rest _ h _ => simp [splitOnDot, h]
  | case4 c rest _ l ls h _ => simp [splitOnDot, h]

private theorem splitOnDot_eq_cons (cs : List Char) :
    ∃ l ls, splitOnDot cs = l :: ls := by
  cases h : splitOnDot cs with
  | nil => exact absurd h (splitOnDot_ne_nil cs)
  | cons l ls => exact ⟨l, ls, rfl⟩

theorem joinWithDot_cons (l : List Char) (ls : List (List Char)) :
    joinWithDot (l :: ls) = l ++ ls.flatMap (fun label => '.' :: label) := rfl

/-- Joining two runs of labels puts a separator between them, which is what makes a label
suffix a separated suffix of the text. -/
theorem joinWithDot_append (before after : List (List Char)) (hb : before ≠ [])
    (ha : after ≠ []) :
    joinWithDot (before ++ after) = joinWithDot before ++ '.' :: joinWithDot after := by
  match before, after with
  | b :: bs, a :: as =>
    simp only [List.cons_append, joinWithDot_cons, List.flatMap_append, List.flatMap_cons,
      List.append_assoc, List.cons_append]

/-- Splitting on the separator and putting it back is the identity, which is what makes a
domain's stored labels a faithful reading of its text. -/
theorem joinWithDot_splitOnDot (cs : List Char) : joinWithDot (splitOnDot cs) = cs := by
  induction cs using splitOnDot.induct with
  | case1 => rfl
  | case2 rest ih =>
    obtain ⟨l, ls, hl⟩ := splitOnDot_eq_cons rest
    rw [hl] at ih
    simp [splitOnDot, hl, joinWithDot_cons] at ih ⊢
    exact ih
  | case3 c rest _ h _ => exact absurd h (splitOnDot_ne_nil rest)
  | case4 c rest _ l ls hl ih =>
    rw [hl] at ih
    simp only [splitOnDot, hl, joinWithDot_cons, List.cons_append] at ih ⊢
    simp [ih]

private theorem foldCase_fixed_on_domain : ∀ c ∈ '.' :: domainChars, foldCase c = c := by decide

private theorem mem_of_isDomainOrDot {c : Char} (h : isDomainOrDot c = true) :
    c ∈ '.' :: domainChars := by
  simp only [isDomainOrDot, isDomainChar, Bool.or_eq_true, beq_iff_eq] at h
  rcases h with h | h
  · exact List.mem_cons_of_mem _ (List.mem_of_elem_eq_true h)
  · simp [h]

/-- Text that has already been folded is unchanged by folding it again, so re-reading a stored
domain reads the same domain (AUTH-16.1, idempotence). -/
private theorem map_foldCase_of_domainChars :
    ∀ cs : List Char, cs.all isDomainOrDot = true → cs.map foldCase = cs
  | [], _ => rfl
  | c :: rest, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    simp [foldCase_fixed_on_domain c (mem_of_isDomainOrDot h.1),
      map_foldCase_of_domainChars rest h.2]

/-- The text a parsed domain renders to is the case-folded text it was parsed from: parsing
changes the spelling of the domain in exactly one way, and rendering undoes nothing else. -/
theorem render_toList {raw : String} {d : Domain} (h : Domain.parse raw = .ok d) :
    d.render.toList = raw.toList.map foldCase := by
  simp only [Domain.parse, Domain.parseFolded] at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · split at h
      · simp at h
      · split at h
        · simp at h
        · simp only [Except.ok.injEq] at h
          subst h
          simp [Domain.render, List.map_map, Function.comp_def, joinWithDot_splitOnDot]

private theorem parsed_chars {raw : String} {d : Domain} (h : Domain.parse raw = .ok d) :
    (raw.toList.map foldCase).all isDomainOrDot = true := by
  simp only [Domain.parse, Domain.parseFolded] at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · split at h
      · simp at h
      · rename_i hall
        simpa using hall

/-- AUTH-16.1: parsing is idempotent. What a parsed domain renders to parses back to it. -/
theorem parse_render {raw : String} {d : Domain} (h : Domain.parse raw = .ok d) :
    Domain.parse d.render = .ok d := by
  simp only [Domain.parse, render_toList h, map_foldCase_of_domainChars _ (parsed_chars h)]
  simpa [Domain.parse] using h

/-- AUTH-16.1 and AUTH-4.5.2: matching cannot distinguish two spellings that differ only in
case, because they are not two inputs. Parsing consumes the folded text and nothing else, so
any two spellings with the same fold parse to the same result, error included. -/
theorem parse_eq_of_fold_eq {s t : String} (h : s.toList.map foldCase = t.toList.map foldCase) :
    Domain.parse s = Domain.parse t := by
  simp [Domain.parse, h]

/-- A parsed domain holds no `@`, which is what lets an address be taken apart at its last one
and put back together again. -/
private theorem at_not_mem_render {raw : String} {d : Domain} (h : Domain.parse raw = .ok d) :
    '@' ∉ d.render.toList := by
  rw [render_toList h]
  intro mem
  have all := parsed_chars h
  simp only [List.all_eq_true] at all
  exact absurd (all '@' mem) (by decide)

private theorem splitAtLastAt_eq_none : ∀ cs : List Char, '@' ∉ cs → splitAtLastAt cs = none
  | [], _ => rfl
  | c :: rest, h => by
    have tail : splitAtLastAt rest = none := splitAtLastAt_eq_none rest (fun m => h (by simp [m]))
    have head : ¬ c = '@' := fun m => h (by simp [m])
    simp [splitAtLastAt, tail, head]

private theorem splitAtLastAt_append :
    ∀ (before after : List Char), '@' ∉ after →
      splitAtLastAt (before ++ '@' :: after) = some (before, after)
  | [], after, h => by simp [splitAtLastAt, splitAtLastAt_eq_none after h]
  | c :: before, after, h => by
    simp [splitAtLastAt, splitAtLastAt_append before after h]

/--
AUTH-16.1: parsing an address is idempotent, and normalisation preserves the sending form of
the local part. The local part travels through unchanged, which is what the theorem's second
half means: nothing between reading an address and sending to it alters the mailbox name
(AUTH-4.5.3).
-/
theorem address_parse_render {raw : String} {a : EmailAddress}
    (h : EmailAddress.parse raw = .ok a) : EmailAddress.parse a.render = .ok a := by
  simp only [EmailAddress.parse] at h
  split at h
  · simp at h
  · rename_i localChars domainChars _
    split at h
    · simp at h
    · split at h
      · simp at h
      · split at h
        · simp at h
        · rename_i notEmpty notUnquoted _ d parsed
          simp only [Except.ok.injEq] at h
          subst h
          have text : (EmailAddress.mk (String.ofList localChars) d).render.toList
              = localChars ++ '@' :: d.render.toList := by
            simp [EmailAddress.render, String.toList_append]
          simp only [EmailAddress.parse, text,
            splitAtLastAt_append _ _ (at_not_mem_render parsed), notEmpty, notUnquoted,
            String.ofList_toList, parse_render parsed]
          rfl

end Tests.Email
