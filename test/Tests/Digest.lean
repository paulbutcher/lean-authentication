/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Authentication.Digest

/-!
The comparison credentials are checked with (AUTH-5.3.4).

Constant time is not a property a theorem here can state, so what is proved is the other half:
that the comparison written for constant time still decides equality. A comparison that leaked
nothing and also accepted the wrong bytes would pass the eye and fail the point.
-/

namespace Tests.Digest
open Authentication

private theorem foldl_and : ∀ (l : List Bool) (acc : Bool), l.foldl Bool.and acc = (acc && l.all id)
  | [], acc => by simp
  | x :: xs, acc => by simp [foldl_and xs, Bool.and_assoc]

theorem bytesEqual_iff : ∀ a b : List UInt8, bytesEqual a b = true ↔ a = b
  | [], [] => by simp [bytesEqual]
  | [], _ :: _ => by simp [bytesEqual]
  | _ :: _, [] => by simp [bytesEqual]
  | x :: xs, y :: ys => by
    have ih := bytesEqual_iff xs ys
    simp only [bytesEqual, foldl_and, Bool.true_and] at ih ⊢
    simp only [List.length_cons, List.zipWith_cons_cons, List.all_cons, Bool.and_eq_true,
      beq_iff_eq, Nat.add_right_cancel_iff, List.cons.injEq, id_eq] at ih ⊢
    constructor
    · rintro ⟨hlen, hx, hrest⟩
      exact ⟨hx, ih.mp ⟨hlen, hrest⟩⟩
    · rintro ⟨hx, hrest⟩
      obtain ⟨hlen, hall⟩ := ih.mpr hrest
      exact ⟨hlen, hx, hall⟩

/-- A digest offered under a key it was not produced with is not a match, whatever its bytes.
This is what lets rotation keep an overlap window instead of a flag day (AUTH-15.7.2). -/
theorem accepts_requires_key (stored : Digest) (bytes : List UInt8) (other : KeyId)
    (h : other ≠ stored.keyId) :
    stored.accepts ⟨[⟨other, bytes⟩]⟩ = false := by
  simp [Digest.accepts, h]

theorem accepts_iff (stored : Digest) (bytes : List UInt8) :
    stored.accepts ⟨[⟨stored.keyId, bytes⟩]⟩ = true ↔ bytes = stored.bytes := by
  simp [Digest.accepts, bytesEqual_iff]

end Tests.Digest
