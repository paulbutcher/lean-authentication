/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Leancrypto.Codec.Base64Url

/-!
What base64url output cannot contain.

Two formats here split text on a separator: the attempt cookie on a colon, and a stored secret on
a dot. Both put base64url in the fields, and both are safe exactly to the extent that the encoder
cannot emit the separator. That is one fact about the alphabet, so it is proved once.
-/

namespace Tests.Base64Url
open Leancrypto.Codec.Base64Url

/--
A character outside the alphabet is not what any sextet encodes to. This is the whole of why a
separator can be trusted to separate: a field that could contain it would be read as two.

`c` is any character, `halpha` says it is not one of the sixty-four the alphabet holds, and `hpad`
that it is not the padding character either. `n` ranges over every natural rather than the
sixty-four that name alphabet positions, so the caller need not first show its index is in range:
beyond the end `encodeSextet` returns the padding character, which `hpad` excludes.
-/
theorem encodeSextet_ne {c : Char} (halpha : c ∉ alphabet) (hpad : c ≠ '=') (n : Nat) :
    encodeSextet n ≠ c := by
  rcases Nat.lt_or_ge n alphabet.length with h | h
  · have : encodeSextet n = alphabet[n] := by
      simp [encodeSextet, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
    rw [this]
    exact fun heq => halpha (heq ▸ List.getElem_mem h)
  · have : encodeSextet n = '=' := by
      simp [encodeSextet, List.getD_eq_getElem?_getD, List.getElem?_eq_none h]
    rw [this]
    exact Ne.symm hpad

/--
The same of an encoding rather than of one sextet: nothing outside the alphabet occurs anywhere in
base64url output. A format that splits on such a character therefore finds exactly the fields it
wrote.

`l` is any byte list and `encode` is the encoder, so the conclusion covers every input length. The
induction follows `encode`'s own recursion, which puts the three short tails, where padding is
emitted, on the same footing as a full group; every character in each comes from `encodeSextet`,
which the theorem above pins away from `c`.
-/
theorem notMem_encode {c : Char} (halpha : c ∉ alphabet) (hpad : c ≠ '=') (l : List UInt8) :
    c ∉ encode l := by
  induction l using encode.induct with
  | case1 => simp [encode]
  | case2 a => simp [encode, encodeSextet_ne halpha hpad, Ne.symm]
  | case3 a b => simp [encode, encodeSextet_ne halpha hpad, Ne.symm]
  | case4 a b c rest ih => simp [encode, encodeSextet_ne halpha hpad, Ne.symm, ih]

/--
The same again for the encoder as it is actually called, on a `ByteArray` and returning a
`String`. Code that builds these formats works in strings, so this is the form it can use without
unfolding anything.

`bytes` is any byte array and the conclusion is that `c` does not occur among the characters of
the encoding. It is the list statement above carried across `String.ofList`, so it holds of arrays
of every length, padding included.
-/
theorem notMem_encodeString {c : Char} (halpha : c ∉ alphabet) (hpad : c ≠ '=')
    (bytes : ByteArray) : c ∉ (encodeString bytes).toList := by
  simp [encodeString, String.toList_ofList, notMem_encode halpha hpad]

end Tests.Base64Url
