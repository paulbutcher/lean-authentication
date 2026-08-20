/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

/-!
Address parsing and normalisation (AUTH-4.5).

Non-ASCII domains are rejected rather than converted to punycode; see `KNOWN_ISSUES.md`.
-/

public section

namespace Authentication

inductive EmailError where
  | missingAt
  | multipleAt
  | emptyLocalPart
  | emptyDomain
  | emptyDomainLabel
  | nonAsciiDomain
  | invalidDomainCharacter
  deriving DecidableEq, Repr

/-- ASCII case folding. Written out rather than taken from `Char.toLower` so that the facts the
address theorems need are decidable. -/
def foldCase : Char → Char
  | 'A' => 'a' | 'B' => 'b' | 'C' => 'c' | 'D' => 'd' | 'E' => 'e' | 'F' => 'f' | 'G' => 'g'
  | 'H' => 'h' | 'I' => 'i' | 'J' => 'j' | 'K' => 'k' | 'L' => 'l' | 'M' => 'm' | 'N' => 'n'
  | 'O' => 'o' | 'P' => 'p' | 'Q' => 'q' | 'R' => 'r' | 'S' => 's' | 'T' => 't' | 'U' => 'u'
  | 'V' => 'v' | 'W' => 'w' | 'X' => 'x' | 'Y' => 'y' | 'Z' => 'z'
  | c => c

def foldCaseString (s : String) : String := String.ofList (s.toList.map foldCase)

def domainChars : List Char := "abcdefghijklmnopqrstuvwxyz0123456789-".toList

def isDomainChar (c : Char) : Bool := domainChars.contains c

def isDomainOrDot (c : Char) : Bool := isDomainChar c || c == '.'

def splitOnDot : List Char → List (List Char)
  | [] => [[]]
  | '.' :: rest => [] :: splitOnDot rest
  | c :: rest =>
    match splitOnDot rest with
    | [] => [[c]]
    | l :: ls => (c :: l) :: ls

def joinWithDot : List (List Char) → List Char
  | [] => []
  | l :: ls => l ++ ls.flatMap (fun label => '.' :: label)

/--
A domain in normal form: case folded, split into labels. Holding the labels rather than the
text is what makes allowlist matching respect label boundaries by construction (AUTH-7.3.1);
there is no spelling of a domain for which a proper suffix of the text can be mistaken for a
suffix of the labels.
-/
structure Domain where
  labels : List String
  deriving DecidableEq, Repr, Inhabited

namespace Domain

def parseFolded (folded : List Char) : Except EmailError Domain :=
  if folded.isEmpty then .error .emptyDomain
  else if folded.any (fun c => c.toNat ≥ 128) then .error .nonAsciiDomain
  else if !folded.all isDomainOrDot then .error .invalidDomainCharacter
  else
    let labels := splitOnDot folded
    if labels.any List.isEmpty then .error .emptyDomainLabel
    else .ok ⟨labels.map String.ofList⟩

/-- Case is folded before anything else is decided, so two spellings differing only in case are
not merely accepted alike: they are the same input from the first line onwards (AUTH-4.5.2). -/
def parse (raw : String) : Except EmailError Domain := parseFolded (raw.toList.map foldCase)

def render (d : Domain) : String := String.ofList (joinWithDot (d.labels.map String.toList))

/-- Whole-label matching. `evilexample.com` does not match `example.com` because the label
lists differ, not because a boundary was checked (AUTH-7.3.1, AUTH-7.3.2). -/
def allows (allowed candidate : Domain) (includeSubdomains : Bool) : Bool :=
  if includeSubdomains then allowed.labels.isSuffixOf candidate.labels
  else allowed.labels == candidate.labels

end Domain

/-- The address as it must be sent: the local part is kept exactly as written (AUTH-4.5.3). -/
structure EmailAddress where
  localPart : String
  domain : Domain
  deriving DecidableEq, Repr, Inhabited

/-- The form two addresses are compared in to decide whether they are the same account. -/
structure NormalisedEmail where
  localPart : String
  domain : Domain
  deriving DecidableEq, Repr, Inhabited

/-- True when the list holds an `@` outside a quoted string. -/
def hasUnquotedAt (chars : List Char) : Bool :=
  go false false chars
where
  go (inQuotes escaped : Bool) : List Char → Bool
    | [] => false
    | c :: rest =>
      if escaped then go inQuotes false rest
      else if c == '\\' && inQuotes then go inQuotes true rest
      else if c == '"' then go (!inQuotes) false rest
      else if c == '@' && !inQuotes then true
      else go inQuotes escaped rest

/-- Splits at the last `@`, so the domain part never contains one. -/
def splitAtLastAt : List Char → Option (List Char × List Char)
  | [] => none
  | c :: rest =>
    match splitAtLastAt rest with
    | some (l, d) => some (c :: l, d)
    | none => if c == '@' then some ([], rest) else none

namespace EmailAddress

def parse (raw : String) : Except EmailError EmailAddress :=
  match splitAtLastAt raw.toList with
  | none => .error .missingAt
  | some (localChars, domainChars) =>
    if localChars.isEmpty then .error .emptyLocalPart
    else if hasUnquotedAt localChars then .error .multipleAt
    else match Domain.parse (String.ofList domainChars) with
      | .error e => .error e
      | .ok d => .ok ⟨String.ofList localChars, d⟩

def render (a : EmailAddress) : String := a.localPart ++ "@" ++ a.domain.render

/-- The local part is compared case-insensitively but sent verbatim: no real provider treats
two spellings as different mailboxes, and treating them as different accounts produces
duplicates nobody can reconcile (AUTH-4.5.3). -/
def normalise (a : EmailAddress) : NormalisedEmail :=
  ⟨foldCaseString a.localPart, a.domain⟩

end EmailAddress

end Authentication
