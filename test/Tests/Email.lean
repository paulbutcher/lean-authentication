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

/--
Splitting text on dots always yields at least one label, the empty string included. Every later
proof about joining takes the split apart with a `match`, and this is what rules out the branch
where there is nothing to match on.

`cs` ranges over all character lists, so the empty one is covered: it splits to `[[]]`, a single
empty label, rather than to no labels at all. The conclusion denies equality with `[]`, the
empty list of labels, which is the only value that would leave `joinWithDot` with nothing to
work from. The induction follows `splitOnDot`'s own recursion, so each of its four cases is
discharged where it arises.
-/
private theorem splitOnDot_ne_nil (cs : List Char) : splitOnDot cs ≠ [] := by
  induction cs using splitOnDot.induct with
  | case1 => simp [splitOnDot]
  | case2 rest _ => simp [splitOnDot]
  | case3 c rest _ h _ => simp [splitOnDot, h]
  | case4 c rest _ l ls h _ => simp [splitOnDot, h]

/--
The split's result is not merely non-empty but visibly a cons, which is the form the proofs
below need in order to rewrite with `joinWithDot_cons`. It packages the previous theorem so that
a proof can obtain the head and tail directly.

`cs` is any character list. The existential produces a first label `l` and a remaining list `ls`
with `splitOnDot cs = l :: ls`. Nothing is claimed about `l` or `ls` beyond their existence; in
particular `l` may be empty, which is what the split gives for text beginning with a dot.
-/
private theorem splitOnDot_eq_cons (cs : List Char) :
    ∃ l ls, splitOnDot cs = l :: ls := by
  cases h : splitOnDot cs with
  | nil => exact absurd h (splitOnDot_ne_nil cs)
  | cons l ls => exact ⟨l, ls, rfl⟩

/--
Joining a non-empty label list is the first label followed by each remaining one preceded by a
dot. This is the definition unfolded once, kept as a named equation so the proofs below can
rewrite with it instead of matching on the list again.

`l` is the first label and `ls` the rest, so `l :: ls` is any non-empty label list. The
right-hand side reads the separator placement off directly: `l` contributes no dot, and every
later label contributes exactly one before itself. It holds by `rfl`, so it introduces no
assumption of its own.
-/
theorem joinWithDot_cons (l : List Char) (ls : List (List Char)) :
    joinWithDot (l :: ls) = l ++ ls.flatMap (fun label => '.' :: label) := rfl

/--
Joining two runs of labels puts a separator between them, which is what makes a label suffix a
separated suffix of the text. This is what the domain matching in `Tests.Policy` reads back to
conclude that `evilexample.com` cannot match `example.com`.

`before` and `after` are label lists, each required to be non-empty by `hb` and `ha`. The
conclusion is that joining the concatenation gives the two joins with an explicit `'.'` between
them. Non-emptiness is what the theorem needs: joining an empty list gives nothing, and the
separator would then be leading or trailing rather than between two labels, so the equation
would be false rather than merely uninteresting.
-/
theorem joinWithDot_append (before after : List (List Char)) (hb : before ≠ [])
    (ha : after ≠ []) :
    joinWithDot (before ++ after) = joinWithDot before ++ '.' :: joinWithDot after := by
  match before, after with
  | b :: bs, a :: as =>
    simp only [List.cons_append, joinWithDot_cons, List.flatMap_append, List.flatMap_cons,
      List.append_assoc, List.cons_append]

/--
Splitting on the separator and putting it back is the identity, which is what makes a domain's
stored labels a faithful reading of its text. A domain is held as labels rather than as text, so
without this the stored form could disagree with what was parsed and rendering would not return
the input.

`cs` is an arbitrary character list, with no assumption that it is a well-formed domain: leading,
trailing and consecutive dots are all covered, and so is the empty list. `splitOnDot` cuts it at
every dot, keeping empty labels where they arise, and `joinWithDot` puts a dot between
consecutive labels. The conclusion is that the round trip returns `cs` itself. Empty labels are
what make it hold in the awkward cases; the parser rejects them separately, but the equality does
not depend on that.
-/
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

/--
Case folding fixes every character a domain is allowed to contain. This is the finite fact
behind idempotence: the case analysis is over thirty-eight characters, so it is settled by
`decide` rather than argued.

The quantifier ranges over `'.' :: domainChars`, the dot together with the lower-case letters,
the digits and the hyphen, which is exactly what `isDomainOrDot` admits. `foldCase c = c` says
each is returned unchanged. The claim is not that `foldCase` is the identity, which it is not;
it is that none of the characters it moves, the twenty-six upper-case letters, is in this list.
-/
private theorem foldCase_fixed_on_domain : ∀ c ∈ '.' :: domainChars, foldCase c = c := by decide

/--
Anything the parser's character check admits is one of the characters folding fixes. It is the
bridge between the `Bool` the parser tests and the membership the folding lemma is stated over.

`h` says `isDomainOrDot c` is `true`, which is the test `parseFolded` applies to every character.
The conclusion places `c` in `'.' :: domainChars`, the same set written as a list so that
`foldCase_fixed_on_domain` applies to it. The two are the same collection by definition; the
proof is the unfolding, and the theorem exists so that unfolding is done once.
-/
private theorem mem_of_isDomainOrDot {c : Char} (h : isDomainOrDot c = true) :
    c ∈ '.' :: domainChars := by
  simp only [isDomainOrDot, isDomainChar, Bool.or_eq_true, beq_iff_eq] at h
  rcases h with h | h
  · exact List.mem_cons_of_mem _ (List.mem_of_elem_eq_true h)
  · simp [h]

/--
Text that has already been folded is unchanged by folding it again, so re-reading a stored
domain reads the same domain (AUTH-16.1, idempotence). This is idempotence of `foldCase` stated
only where it is needed, over the characters a domain may contain.

`cs` is a character list and the hypothesis is that every one of its characters satisfies
`isDomainOrDot`, which is the lower-case letters, the digits, the hyphen and the dot. The
conclusion is that mapping `foldCase` over it returns it unchanged. The hypothesis is what makes
this true rather than trivial: `foldCase` moves the upper-case letters, and none of them is a
domain character, so a list that passed the parser's check has nothing left to fold.
-/
private theorem map_foldCase_of_domainChars :
    ∀ cs : List Char, cs.all isDomainOrDot = true → cs.map foldCase = cs
  | [], _ => rfl
  | c :: rest, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    simp [foldCase_fixed_on_domain c (mem_of_isDomainOrDot h.1),
      map_foldCase_of_domainChars rest h.2]

/--
The text a parsed domain renders to is the case-folded text it was parsed from: parsing changes
the spelling of the domain in exactly one way, and rendering undoes nothing else. Everything
else the parser does, splitting into labels and checking them, is invisible in the output.

`h` says `raw` parsed to `d`. `d.render` joins the stored labels back with dots, and the
conclusion equates its characters with `raw.toList.map foldCase`, the input with case folded and
nothing else done to it. Rendering is therefore not merely something that parses back; it is the
folded input character for character. The splitting and rejoining cancel by
`joinWithDot_splitOnDot`, which is why no label boundary is moved or lost.
-/
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

/--
Every character of a domain the parser accepted is a domain character or a dot. This is what
`parse_render` needs to know that folding the rendered text a second time is the identity, and
what `at_not_mem_render` needs to rule out an `@`.

`h` says `raw` parsed to some `d`. The conclusion is about `raw.toList.map foldCase`, the folded
input rather than the domain, because that is the list `parseFolded` inspected. `isDomainOrDot`
answers `true` for the thirty-seven characters in `domainChars`, which are the lower-case
letters, the digits and the hyphen, and for `'.'`. So an accepted parse means the character check
inside `parseFolded` passed, which is the branch the proof isolates.
-/
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

/--
AUTH-16.1: parsing is idempotent. What a parsed domain renders to parses back to it, so a domain
that has been through storage, a URL, or a mail header is the same domain when it is read again.

`h` says `raw` parsed to `d`, so the claim is about domains the parser produced. The conclusion
is `.ok d` on the nose: parsing the rendered text neither fails nor yields a different label
list. It follows from `render_toList`, which says the rendered text is the folded input, and
`map_foldCase_of_domainChars`, which says folding it a second time changes nothing, so the
second parse sees the characters the first one already decided on.
-/
theorem parse_render {raw : String} {d : Domain} (h : Domain.parse raw = .ok d) :
    Domain.parse d.render = .ok d := by
  simp only [Domain.parse, render_toList h, map_foldCase_of_domainChars _ (parsed_chars h)]
  simpa [Domain.parse] using h

/--
AUTH-16.1 and AUTH-4.5.2: matching cannot distinguish two spellings that differ only in case,
because they are not two inputs. Parsing consumes the folded text and nothing else, so any two
spellings with the same fold parse to the same result, error included.

`h` says the two strings have the same case-folded characters; `foldCase` maps `A`-`Z` to
lower case and fixes everything else, so this is exactly "differ only in case". The conclusion
equates the two `Except` results outright. Because it is the whole result and not just the
success case, a spelling that is rejected is rejected in the same way with the same error, which
is what stops case being usable to tell one refusal from another.
-/
theorem parse_eq_of_fold_eq {s t : String} (h : s.toList.map foldCase = t.toList.map foldCase) :
    Domain.parse s = Domain.parse t := by
  simp [Domain.parse, h]

/--
A parsed domain holds no `@`, which is what lets an address be taken apart at its last one and
put back together again. Without it, rendering an address could produce text that splits
somewhere else, and the address round trip would fail on exactly the inputs an attacker chooses.

`h` says `raw` parsed to the domain `d`, so this is a claim about domains the parser produced
and not about arbitrary label lists. The conclusion is that `'@'` does not occur in the
characters of `d.render`. It follows from `parsed_chars`: every character of a parsed domain
satisfies `isDomainOrDot`, and `@` is neither a domain character nor a dot.
-/
private theorem at_not_mem_render {raw : String} {d : Domain} (h : Domain.parse raw = .ok d) :
    '@' ∉ d.render.toList := by
  rw [render_toList h]
  intro mem
  have all := parsed_chars h
  simp only [List.all_eq_true] at all
  exact absurd (all '@' mem) (by decide)

/--
Text with no `@` in it does not split, and does so by returning `none` rather than an empty or
arbitrary pair. `splitAtLastAt` searching from the right makes this the base case the append
lemma below rests on.

`cs` is any character list and the hypothesis is that `'@'` is not among its elements. The
conclusion is `none` exactly, which is the value `EmailAddress.parse` turns into
`.error .missingAt`, so the failure is reported rather than guessed at. The empty list satisfies
the hypothesis and is the recursion's base; the step supplies both that the head is not `@` and
that the tail has none either.
-/
private theorem splitAtLastAt_eq_none : ∀ cs : List Char, '@' ∉ cs → splitAtLastAt cs = none
  | [], _ => rfl
  | c :: rest, h => by
    have tail : splitAtLastAt rest = none := splitAtLastAt_eq_none rest (fun m => h (by simp [m]))
    have head : ¬ c = '@' := fun m => h (by simp [m])
    simp [splitAtLastAt, tail, head]

/--
An address is split at its last `@` exactly where one would expect when nothing after that
point is another `@`. This is the step that makes `render` invert `parse` for the address as a
whole, since rendering rebuilds precisely this shape.

`before` and `after` are arbitrary character lists and `h` says `after` holds no `@`, which is
what `at_not_mem_render` establishes for a parsed domain. `splitAtLastAt` returns the pair
either side of the last `@`, or `none` when there is none. The conclusion pins it to `some
(before, after)`: the split lands at the `@` that was written between them, so a local part
containing its own `@` characters, which `before` may, is not divided at the wrong one.
-/
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

`h` says `raw` parsed to `a`, so the hypothesis is about addresses the parser actually accepts
rather than about arbitrary values of `EmailAddress`. `a.render` puts the parts back together as
`localPart ++ "@" ++ domain.render`. The conclusion is `.ok a` and not merely `.ok` of something
that parses: the same address, so a round trip through storage or a mail header returns the
record it started as. The local part's preservation is carried by the equality being with `a`
itself, whose `localPart` is the text as written; only the domain was folded, and only on the
first parse.
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
