/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Authentication.Codec.Base32
import Authentication.Codec.Base64Url

/-!
Round-trip theorems for the two encodings (AUTH-16.1).

Two shapes here are for elaboration cost rather than clarity, and both matter: the file is
minutes slower without them. `decode` is unfolded through `rfl` lemmas, because applying the
equation lemmas of a match over list literals of several lengths is expensive. And the
character-level rewrites are packaged into one lemma per group, stated over quintet variables,
so that the group values appear in a rewrite only after unification has already fixed them;
rewriting under `simp` with the arithmetic in place makes every failed match an attempt to
unfold the alphabet.
-/

namespace Tests.Codec

namespace Base32
open Authentication.Codec.Base32

private theorem quintet_roundTrip : ∀ n ∈ List.range 32, decodeChar (encodeQuintet n) = some n := by
  decide

private theorem qr {n : Nat} (h : n < 32) : decodeChar (encodeQuintet n) = some n :=
  quintet_roundTrip n (List.mem_range.mpr h)

private theorem decode_2 (x y : Char) : decode [x, y] =
    match decodeChar x, decodeChar y with
    | some q0, some q1 => oneByte q0 q1
    | _, _ => none := rfl

private theorem decode_4 (x y z w : Char) : decode [x, y, z, w] =
    match decodeChar x, decodeChar y, decodeChar z, decodeChar w with
    | some q0, some q1, some q2, some q3 => twoBytes q0 q1 q2 q3
    | _, _, _, _ => none := rfl

private theorem decode_5 (x y z w v : Char) : decode [x, y, z, w, v] =
    match decodeChar x, decodeChar y, decodeChar z, decodeChar w, decodeChar v with
    | some q0, some q1, some q2, some q3, some q4 => threeBytes q0 q1 q2 q3 q4
    | _, _, _, _, _ => none := rfl

private theorem decode_7 (x y z w v u t : Char) : decode [x, y, z, w, v, u, t] =
    match decodeChar x, decodeChar y, decodeChar z, decodeChar w, decodeChar v, decodeChar u,
        decodeChar t with
    | some q0, some q1, some q2, some q3, some q4, some q5, some q6 =>
      fourBytes q0 q1 q2 q3 q4 q5 q6
    | _, _, _, _, _, _, _ => none := rfl

private theorem decode_8 (x y z w v u t s : Char) (rest : List Char) :
    decode (x :: y :: z :: w :: v :: u :: t :: s :: rest) =
    match decodeChar x, decodeChar y, decodeChar z, decodeChar w, decodeChar v, decodeChar u,
        decodeChar t, decodeChar s, decode rest with
    | some q0, some q1, some q2, some q3, some q4, some q5, some q6, some q7, some tail =>
      some (fiveBytes q0 q1 q2 q3 q4 q5 q6 q7 ++ tail)
    | _, _, _, _, _, _, _, _, _ => none := rfl

private theorem group1 {q0 q1 : Nat} (h0 : q0 < 32) (h1 : q1 < 32) :
    decode [encodeQuintet q0, encodeQuintet q1] = oneByte q0 q1 := by
  simp only [decode_2, qr h0, qr h1]

private theorem group2 {q0 q1 q2 q3 : Nat} (h0 : q0 < 32) (h1 : q1 < 32) (h2 : q2 < 32)
    (h3 : q3 < 32) :
    decode [encodeQuintet q0, encodeQuintet q1, encodeQuintet q2, encodeQuintet q3]
      = twoBytes q0 q1 q2 q3 := by
  simp only [decode_4, qr h0, qr h1, qr h2, qr h3]

private theorem group3 {q0 q1 q2 q3 q4 : Nat} (h0 : q0 < 32) (h1 : q1 < 32) (h2 : q2 < 32)
    (h3 : q3 < 32) (h4 : q4 < 32) :
    decode [encodeQuintet q0, encodeQuintet q1, encodeQuintet q2, encodeQuintet q3,
      encodeQuintet q4] = threeBytes q0 q1 q2 q3 q4 := by
  simp only [decode_5, qr h0, qr h1, qr h2, qr h3, qr h4]

private theorem group4 {q0 q1 q2 q3 q4 q5 q6 : Nat} (h0 : q0 < 32) (h1 : q1 < 32) (h2 : q2 < 32)
    (h3 : q3 < 32) (h4 : q4 < 32) (h5 : q5 < 32) (h6 : q6 < 32) :
    decode [encodeQuintet q0, encodeQuintet q1, encodeQuintet q2, encodeQuintet q3,
      encodeQuintet q4, encodeQuintet q5, encodeQuintet q6] = fourBytes q0 q1 q2 q3 q4 q5 q6 := by
  simp only [decode_7, qr h0, qr h1, qr h2, qr h3, qr h4, qr h5, qr h6]

private theorem group5 {q0 q1 q2 q3 q4 q5 q6 q7 : Nat} (h0 : q0 < 32) (h1 : q1 < 32)
    (h2 : q2 < 32) (h3 : q3 < 32) (h4 : q4 < 32) (h5 : q5 < 32) (h6 : q6 < 32) (h7 : q7 < 32)
    {cs : List Char} {tail : List UInt8} (hcs : decode cs = some tail) :
    decode (encodeQuintet q0 :: encodeQuintet q1 :: encodeQuintet q2 :: encodeQuintet q3
        :: encodeQuintet q4 :: encodeQuintet q5 :: encodeQuintet q6 :: encodeQuintet q7 :: cs)
      = some (fiveBytes q0 q1 q2 q3 q4 q5 q6 q7 ++ tail) := by
  simp only [decode_8, qr h0, qr h1, qr h2, qr h3, qr h4, qr h5, qr h6, qr h7, hcs]

private theorem rt1 (a : UInt8) : decode (encode [a]) = some [a] := by
  have ha : a.toNat < 256 := a.toNat_lt_size
  simp only [encode]
  rw [group1 (by omega : a.toNat / 8 < 32) (by omega : a.toNat % 8 * 4 < 32), oneByte,
    show a.toNat % 8 * 4 % 4 = 0 by omega,
    show a.toNat / 8 * 8 + a.toNat % 8 * 4 / 4 = a.toNat by omega, UInt8.ofNat_toNat]
  rfl

private theorem rt2 (a b : UInt8) : decode (encode [a, b]) = some [a, b] := by
  have ha : a.toNat < 256 := a.toNat_lt_size
  have hb : b.toNat < 256 := b.toNat_lt_size
  simp only [encode]
  rw [group2 (by omega : (a.toNat * 256 + b.toNat) / 2048 < 32)
      (by omega : (a.toNat * 256 + b.toNat) / 64 % 32 < 32)
      (by omega : (a.toNat * 256 + b.toNat) / 2 % 32 < 32)
      (by omega : (a.toNat * 256 + b.toNat) % 2 * 16 < 32),
    twoBytes,
    show (a.toNat * 256 + b.toNat) % 2 * 16 % 16 = 0 by omega,
    show (a.toNat * 256 + b.toNat) / 2048 * 8 + (a.toNat * 256 + b.toNat) / 64 % 32 / 4
      = a.toNat by omega,
    show (a.toNat * 256 + b.toNat) / 64 % 32 % 4 * 64 + (a.toNat * 256 + b.toNat) / 2 % 32 * 2
      + (a.toNat * 256 + b.toNat) % 2 * 16 / 16 = b.toNat by omega]
  simp only [UInt8.ofNat_toNat]
  rfl

private theorem rt3 (a b c : UInt8) : decode (encode [a, b, c]) = some [a, b, c] := by
  have ha : a.toNat < 256 := a.toNat_lt_size
  have hb : b.toNat < 256 := b.toNat_lt_size
  have hc : c.toNat < 256 := c.toNat_lt_size
  simp only [encode]
  rw [group3 (by omega : (a.toNat * 65536 + b.toNat * 256 + c.toNat) / 524288 < 32)
      (by omega : (a.toNat * 65536 + b.toNat * 256 + c.toNat) / 16384 % 32 < 32)
      (by omega : (a.toNat * 65536 + b.toNat * 256 + c.toNat) / 512 % 32 < 32)
      (by omega : (a.toNat * 65536 + b.toNat * 256 + c.toNat) / 16 % 32 < 32)
      (by omega : (a.toNat * 65536 + b.toNat * 256 + c.toNat) % 16 * 2 < 32),
    threeBytes,
    show (a.toNat * 65536 + b.toNat * 256 + c.toNat) % 16 * 2 % 2 = 0 by omega,
    show (a.toNat * 65536 + b.toNat * 256 + c.toNat) / 524288 * 8
      + (a.toNat * 65536 + b.toNat * 256 + c.toNat) / 16384 % 32 / 4 = a.toNat by omega,
    show (a.toNat * 65536 + b.toNat * 256 + c.toNat) / 16384 % 32 % 4 * 64
      + (a.toNat * 65536 + b.toNat * 256 + c.toNat) / 512 % 32 * 2
      + (a.toNat * 65536 + b.toNat * 256 + c.toNat) / 16 % 32 / 16 = b.toNat by omega,
    show (a.toNat * 65536 + b.toNat * 256 + c.toNat) / 16 % 32 % 16 * 16
      + (a.toNat * 65536 + b.toNat * 256 + c.toNat) % 16 * 2 / 2 = c.toNat by omega]
  simp only [UInt8.ofNat_toNat]
  rfl

private theorem rt4 (a b c d : UInt8) : decode (encode [a, b, c, d]) = some [a, b, c, d] := by
  have ha : a.toNat < 256 := a.toNat_lt_size
  have hb : b.toNat < 256 := b.toNat_lt_size
  have hc : c.toNat < 256 := c.toNat_lt_size
  have hd : d.toNat < 256 := d.toNat_lt_size
  simp only [encode]
  rw [group4
      (by omega : (a.toNat * 16777216 + b.toNat * 65536 + c.toNat * 256 + d.toNat) / 134217728 < 32)
      (by omega : (a.toNat * 16777216 + b.toNat * 65536 + c.toNat * 256 + d.toNat) / 4194304 % 32 < 32)
      (by omega : (a.toNat * 16777216 + b.toNat * 65536 + c.toNat * 256 + d.toNat) / 131072 % 32 < 32)
      (by omega : (a.toNat * 16777216 + b.toNat * 65536 + c.toNat * 256 + d.toNat) / 4096 % 32 < 32)
      (by omega : (a.toNat * 16777216 + b.toNat * 65536 + c.toNat * 256 + d.toNat) / 128 % 32 < 32)
      (by omega : (a.toNat * 16777216 + b.toNat * 65536 + c.toNat * 256 + d.toNat) / 4 % 32 < 32)
      (by omega : (a.toNat * 16777216 + b.toNat * 65536 + c.toNat * 256 + d.toNat) % 4 * 8 < 32),
    fourBytes,
    show (a.toNat * 16777216 + b.toNat * 65536 + c.toNat * 256 + d.toNat) % 4 * 8 % 8 = 0 by omega,
    show (a.toNat * 16777216 + b.toNat * 65536 + c.toNat * 256 + d.toNat) / 134217728 * 8
      + (a.toNat * 16777216 + b.toNat * 65536 + c.toNat * 256 + d.toNat) / 4194304 % 32 / 4
      = a.toNat by omega,
    show (a.toNat * 16777216 + b.toNat * 65536 + c.toNat * 256 + d.toNat) / 4194304 % 32 % 4 * 64
      + (a.toNat * 16777216 + b.toNat * 65536 + c.toNat * 256 + d.toNat) / 131072 % 32 * 2
      + (a.toNat * 16777216 + b.toNat * 65536 + c.toNat * 256 + d.toNat) / 4096 % 32 / 16
      = b.toNat by omega,
    show (a.toNat * 16777216 + b.toNat * 65536 + c.toNat * 256 + d.toNat) / 4096 % 32 % 16 * 16
      + (a.toNat * 16777216 + b.toNat * 65536 + c.toNat * 256 + d.toNat) / 128 % 32 / 2
      = c.toNat by omega,
    show (a.toNat * 16777216 + b.toNat * 65536 + c.toNat * 256 + d.toNat) / 128 % 32 % 2 * 128
      + (a.toNat * 16777216 + b.toNat * 65536 + c.toNat * 256 + d.toNat) / 4 % 32 * 4
      + (a.toNat * 16777216 + b.toNat * 65536 + c.toNat * 256 + d.toNat) % 4 * 8 / 8
      = d.toNat by omega]
  simp only [UInt8.ofNat_toNat]
  rfl

private theorem rt5 (a b c d e : UInt8) (rest : List UInt8)
    (ih : decode (encode rest) = some rest) :
    decode (encode (a :: b :: c :: d :: e :: rest)) = some (a :: b :: c :: d :: e :: rest) := by
  have ha : a.toNat < 256 := a.toNat_lt_size
  have hb : b.toNat < 256 := b.toNat_lt_size
  have hc : c.toNat < 256 := c.toNat_lt_size
  have hd : d.toNat < 256 := d.toNat_lt_size
  have he : e.toNat < 256 := e.toNat_lt_size
  simp only [encode]
  rw [group5
      (by omega : (a.toNat * 4294967296 + b.toNat * 16777216 + c.toNat * 65536 + d.toNat * 256
        + e.toNat) / 34359738368 < 32)
      (by omega : (a.toNat * 4294967296 + b.toNat * 16777216 + c.toNat * 65536 + d.toNat * 256
        + e.toNat) / 1073741824 % 32 < 32)
      (by omega : (a.toNat * 4294967296 + b.toNat * 16777216 + c.toNat * 65536 + d.toNat * 256
        + e.toNat) / 33554432 % 32 < 32)
      (by omega : (a.toNat * 4294967296 + b.toNat * 16777216 + c.toNat * 65536 + d.toNat * 256
        + e.toNat) / 1048576 % 32 < 32)
      (by omega : (a.toNat * 4294967296 + b.toNat * 16777216 + c.toNat * 65536 + d.toNat * 256
        + e.toNat) / 32768 % 32 < 32)
      (by omega : (a.toNat * 4294967296 + b.toNat * 16777216 + c.toNat * 65536 + d.toNat * 256
        + e.toNat) / 1024 % 32 < 32)
      (by omega : (a.toNat * 4294967296 + b.toNat * 16777216 + c.toNat * 65536 + d.toNat * 256
        + e.toNat) / 32 % 32 < 32)
      (by omega : (a.toNat * 4294967296 + b.toNat * 16777216 + c.toNat * 65536 + d.toNat * 256
        + e.toNat) % 32 < 32) ih,
    fiveBytes,
    show (a.toNat * 4294967296 + b.toNat * 16777216 + c.toNat * 65536 + d.toNat * 256
        + e.toNat) / 34359738368 * 8
      + (a.toNat * 4294967296 + b.toNat * 16777216 + c.toNat * 65536 + d.toNat * 256
        + e.toNat) / 1073741824 % 32 / 4 = a.toNat by omega,
    show (a.toNat * 4294967296 + b.toNat * 16777216 + c.toNat * 65536 + d.toNat * 256
        + e.toNat) / 1073741824 % 32 % 4 * 64
      + (a.toNat * 4294967296 + b.toNat * 16777216 + c.toNat * 65536 + d.toNat * 256
        + e.toNat) / 33554432 % 32 * 2
      + (a.toNat * 4294967296 + b.toNat * 16777216 + c.toNat * 65536 + d.toNat * 256
        + e.toNat) / 1048576 % 32 / 16 = b.toNat by omega,
    show (a.toNat * 4294967296 + b.toNat * 16777216 + c.toNat * 65536 + d.toNat * 256
        + e.toNat) / 1048576 % 32 % 16 * 16
      + (a.toNat * 4294967296 + b.toNat * 16777216 + c.toNat * 65536 + d.toNat * 256
        + e.toNat) / 32768 % 32 / 2 = c.toNat by omega,
    show (a.toNat * 4294967296 + b.toNat * 16777216 + c.toNat * 65536 + d.toNat * 256
        + e.toNat) / 32768 % 32 % 2 * 128
      + (a.toNat * 4294967296 + b.toNat * 16777216 + c.toNat * 65536 + d.toNat * 256
        + e.toNat) / 1024 % 32 * 4
      + (a.toNat * 4294967296 + b.toNat * 16777216 + c.toNat * 65536 + d.toNat * 256
        + e.toNat) / 32 % 32 / 8 = d.toNat by omega,
    show (a.toNat * 4294967296 + b.toNat * 16777216 + c.toNat * 65536 + d.toNat * 256
        + e.toNat) / 32 % 32 % 8 * 32
      + (a.toNat * 4294967296 + b.toNat * 16777216 + c.toNat * 65536 + d.toNat * 256
        + e.toNat) % 32 = e.toNat by omega]
  simp only [UInt8.ofNat_toNat, List.cons_append, List.nil_append]

theorem decode_encode (bytes : List UInt8) : decode (encode bytes) = some bytes := by
  induction bytes using encode.induct with
  | case1 => rfl
  | case2 a => exact rt1 a
  | case3 a b => exact rt2 a b
  | case4 a b c => exact rt3 a b c
  | case5 a b c d => exact rt4 a b c d
  | case6 a b c d e rest ih => exact rt5 a b c d e rest ih

end Base32

namespace Base64Url
open Authentication.Codec.Base64Url

private theorem sextet_roundTrip : ∀ n ∈ List.range 64, decodeChar (encodeSextet n) = some n := by
  decide

private theorem sr {n : Nat} (h : n < 64) : decodeChar (encodeSextet n) = some n :=
  sextet_roundTrip n (List.mem_range.mpr h)

private theorem decode_2 (x y : Char) : decode [x, y] =
    match decodeChar x, decodeChar y with
    | some s0, some s1 => oneByte s0 s1
    | _, _ => none := rfl

private theorem decode_3 (x y z : Char) : decode [x, y, z] =
    match decodeChar x, decodeChar y, decodeChar z with
    | some s0, some s1, some s2 => twoBytes s0 s1 s2
    | _, _, _ => none := rfl

private theorem decode_4 (x y z w : Char) (rest : List Char) :
    decode (x :: y :: z :: w :: rest) =
    match decodeChar x, decodeChar y, decodeChar z, decodeChar w, decode rest with
    | some s0, some s1, some s2, some s3, some tail => some (threeBytes s0 s1 s2 s3 ++ tail)
    | _, _, _, _, _ => none := rfl

private theorem group1 {s0 s1 : Nat} (h0 : s0 < 64) (h1 : s1 < 64) :
    decode [encodeSextet s0, encodeSextet s1] = oneByte s0 s1 := by
  simp only [decode_2, sr h0, sr h1]

private theorem group2 {s0 s1 s2 : Nat} (h0 : s0 < 64) (h1 : s1 < 64) (h2 : s2 < 64) :
    decode [encodeSextet s0, encodeSextet s1, encodeSextet s2] = twoBytes s0 s1 s2 := by
  simp only [decode_3, sr h0, sr h1, sr h2]

private theorem group3 {s0 s1 s2 s3 : Nat} (h0 : s0 < 64) (h1 : s1 < 64) (h2 : s2 < 64)
    (h3 : s3 < 64) {cs : List Char} {tail : List UInt8} (hcs : decode cs = some tail) :
    decode (encodeSextet s0 :: encodeSextet s1 :: encodeSextet s2 :: encodeSextet s3 :: cs)
      = some (threeBytes s0 s1 s2 s3 ++ tail) := by
  simp only [decode_4, sr h0, sr h1, sr h2, sr h3, hcs]

private theorem rt1 (a : UInt8) : decode (encode [a]) = some [a] := by
  have ha : a.toNat < 256 := a.toNat_lt_size
  simp only [encode]
  rw [group1 (by omega : a.toNat / 4 < 64) (by omega : a.toNat % 4 * 16 < 64), oneByte,
    show a.toNat % 4 * 16 % 16 = 0 by omega,
    show a.toNat / 4 * 4 + a.toNat % 4 * 16 / 16 = a.toNat by omega, UInt8.ofNat_toNat]
  rfl

private theorem rt2 (a b : UInt8) : decode (encode [a, b]) = some [a, b] := by
  have ha : a.toNat < 256 := a.toNat_lt_size
  have hb : b.toNat < 256 := b.toNat_lt_size
  simp only [encode]
  rw [group2 (by omega : (a.toNat * 256 + b.toNat) / 1024 < 64)
      (by omega : (a.toNat * 256 + b.toNat) / 16 % 64 < 64)
      (by omega : (a.toNat * 256 + b.toNat) % 16 * 4 < 64),
    twoBytes,
    show (a.toNat * 256 + b.toNat) % 16 * 4 % 4 = 0 by omega,
    show (a.toNat * 256 + b.toNat) / 1024 * 4 + (a.toNat * 256 + b.toNat) / 16 % 64 / 16
      = a.toNat by omega,
    show (a.toNat * 256 + b.toNat) / 16 % 64 % 16 * 16 + (a.toNat * 256 + b.toNat) % 16 * 4 / 4
      = b.toNat by omega]
  simp only [UInt8.ofNat_toNat]
  rfl

private theorem rt3 (a b c : UInt8) (rest : List UInt8)
    (ih : decode (encode rest) = some rest) :
    decode (encode (a :: b :: c :: rest)) = some (a :: b :: c :: rest) := by
  have ha : a.toNat < 256 := a.toNat_lt_size
  have hb : b.toNat < 256 := b.toNat_lt_size
  have hc : c.toNat < 256 := c.toNat_lt_size
  simp only [encode]
  rw [group3 (by omega : (a.toNat * 65536 + b.toNat * 256 + c.toNat) / 262144 < 64)
      (by omega : (a.toNat * 65536 + b.toNat * 256 + c.toNat) / 4096 % 64 < 64)
      (by omega : (a.toNat * 65536 + b.toNat * 256 + c.toNat) / 64 % 64 < 64)
      (by omega : (a.toNat * 65536 + b.toNat * 256 + c.toNat) % 64 < 64) ih,
    threeBytes,
    show (a.toNat * 65536 + b.toNat * 256 + c.toNat) / 262144 * 4
      + (a.toNat * 65536 + b.toNat * 256 + c.toNat) / 4096 % 64 / 16 = a.toNat by omega,
    show (a.toNat * 65536 + b.toNat * 256 + c.toNat) / 4096 % 64 % 16 * 16
      + (a.toNat * 65536 + b.toNat * 256 + c.toNat) / 64 % 64 / 4 = b.toNat by omega,
    show (a.toNat * 65536 + b.toNat * 256 + c.toNat) / 64 % 64 % 4 * 64
      + (a.toNat * 65536 + b.toNat * 256 + c.toNat) % 64 = c.toNat by omega]
  simp only [UInt8.ofNat_toNat, List.cons_append, List.nil_append]

theorem decode_encode (bytes : List UInt8) : decode (encode bytes) = some bytes := by
  induction bytes using encode.induct with
  | case1 => rfl
  | case2 a => exact rt1 a
  | case3 a b => exact rt2 a b
  | case4 a b c rest ih => exact rt3 a b c rest ih

end Base64Url

end Tests.Codec
