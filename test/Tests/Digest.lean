/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Authentication.Digest

/-!
The comparison credentials are checked with (AUTH-5.3.4).

Absence of an early exit is not a property a theorem here can state, so what is proved is the
other half: that the comparison written to avoid one still decides equality. A comparison that
leaked nothing and also accepted the wrong bytes would pass the eye and fail the point.

`bytesEqual_iff` is a fact about `Crypto.bytesEqual`, which belongs to a dependency, and is
restated here because `accepts_iff` needs it and that library proves it in its own suite rather
than exporting it. Its proper home is beside the definition.
-/

namespace Tests.Digest
open Authentication

/--
Folding `Bool.and` over a list of results is the conjunction of the accumulator with all of
them. This is the rewrite that turns the comparison's fold into something an induction on two
lists can use, and it is stated once here rather than repeated at each use.

`l` is the list of per-byte results and `acc` the accumulator the fold starts from, left
arbitrary so the lemma applies at every step of the fold as well as at its start. The right-hand
side is `acc && l.all id`, where `List.all id` answers `true` when every element is `true`.
Nothing is claimed about evaluation order or about when the fold stops looking; the comparison's
lack of an early exit is a property of the code, not of this equation.
-/
private theorem foldl_and : ∀ (l : List Bool) (acc : Bool), l.foldl Bool.and acc = (acc && l.all id)
  | [], acc => by simp
  | x :: xs, acc => by simp [foldl_and xs, Bool.and_assoc]

/--
The same statement at the level of lists, where the induction can be written. It is the whole
content of `bytesEqual_iff`: a `ByteArray` is a wrapper around an array, so unfolding the
comparison leaves exactly this.

`a` and `b` are arbitrary byte lists. The left-hand side is the comparison as written: lengths
compared first, then the pairwise results of `zipWith` folded with `Bool.and` from `true`. The
length test is what makes the fold sound, since `zipWith` stops at the shorter list and would
otherwise report `true` for a prefix; the four cases in the proof are the two empty lists, the
two mismatched ones, and the step. The right-hand side is equality of the lists, so the two are
shown to agree in both directions.
-/
private theorem list_iff : ∀ a b : List UInt8,
    ((a.length == b.length) && (List.zipWith (fun x y => x == y) a b).foldl Bool.and true) = true
      ↔ a = b
  | [], [] => by simp
  | [], _ :: _ => by simp
  | _ :: _, [] => by simp
  | x :: xs, y :: ys => by
    have ih := list_iff xs ys
    simp only [foldl_and, Bool.true_and] at ih ⊢
    simp only [List.length_cons, List.zipWith_cons_cons, List.all_cons, Bool.and_eq_true,
      beq_iff_eq, Nat.add_right_cancel_iff, List.cons.injEq, id_eq] at ih ⊢
    constructor
    · rintro ⟨hlen, hx, hrest⟩
      exact ⟨hx, ih.mp ⟨hlen, hrest⟩⟩
    · rintro ⟨hx, hrest⟩
      obtain ⟨hlen, hall⟩ := ih.mpr hrest
      exact ⟨hlen, hx, hall⟩

/--
`Crypto.bytesEqual` answers `true` exactly on equal byte arrays. `accepts_iff` below rests on
it, and the library that defines the comparison proves this in its own suite rather than
exporting it, so it is restated here; its proper home is beside the definition.

`a` and `b` range over all of `ByteArray`, with no assumption that they are the same length. The
biconditional is what is needed in both directions: `true` only for equal arrays, so nothing
unequal is admitted, and `true` for every equal pair, so nothing equal is refused. Equality here
is equality of the arrays themselves, not of their lengths or of some prefix.
-/
theorem bytesEqual_iff : ∀ a b : ByteArray, Crypto.bytesEqual a b = true ↔ a = b
  | ⟨da⟩, ⟨db⟩ => by
    simp only [Crypto.bytesEqual, ByteArray.size, ByteArray.mk.injEq, ← Array.length_toList,
      list_iff, Array.toList_inj]

/--
A digest offered under a key it was not produced with is not a match, whatever its bytes. This
is what lets rotation keep an overlap window instead of a flag day (AUTH-15.7.2): a secret
digested under a retired pepper is refused rather than compared against a current one.

`stored` is the digest held against the record, and `⟨[⟨other, bytes⟩]⟩` is a presented secret
carrying a single digest under `other`. `h` says `other` is not the key `stored` was produced
with. `bytes` is unconstrained and may be exactly `stored.bytes`, which is the case worth
covering: the answer is `false` because the key lookup inside `accepts` finds nothing, so the
comparison never happens. `Digest.accepts` returns `Bool`, and the conclusion pins it at `false`
rather than merely denying `true`.
-/
theorem accepts_requires_key (stored : Digest) (bytes : ByteArray) (other : KeyId)
    (h : other ≠ stored.keyId) :
    stored.accepts ⟨[⟨other, bytes⟩]⟩ = false := by
  simp [Digest.accepts, h]

/--
The constant-time comparison still decides equality: a credential is accepted exactly when its
bytes are the stored ones. This is the half of AUTH-5.3.4 a theorem can reach. A comparison that
leaked nothing and accepted the wrong bytes would look right and be worthless, and this rules
that out.

`stored` is the digest held against the record and `⟨[⟨stored.keyId, bytes⟩]⟩` is a presented
secret offering one digest under the very key the stored one was produced with, so the key
lookup inside `accepts` succeeds and what remains is the byte comparison alone. The biconditional
gives both directions: acceptance implies the bytes are equal, so no wrong secret is admitted,
and equality implies acceptance, so no correct one is turned away. `bytes` is unconstrained,
including in length, so a truncated or overlong offering is covered.
-/
theorem accepts_iff (stored : Digest) (bytes : ByteArray) :
    stored.accepts ⟨[⟨stored.keyId, bytes⟩]⟩ = true ↔ bytes = stored.bytes := by
  simp [Digest.accepts, bytesEqual_iff]

end Tests.Digest
