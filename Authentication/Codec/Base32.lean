/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
Crockford base32.

The alphabet omits `I`, `L`, `O` and `U`, so a code read aloud or copied off a screen has no
confusable pair, and `U` cannot appear inside an accidental obscenity. Decoding is deliberately
more generous than encoding: it folds case and accepts the characters a reader is likely to
substitute, because the code exists to be transcribed by hand.

Trailing bits outside the encoded bytes are required to be zero, so a byte string has exactly
one accepted encoding.
-/

namespace Authentication.Codec.Base32

def alphabet : List Char := "0123456789ABCDEFGHJKMNPQRSTVWXYZ".toList

def encodeQuintet (n : Nat) : Char := alphabet.getD n '='

/-- Folds the substitutions a person makes when transcribing: case, `I`/`L` for `1`, `O` for `0`. -/
def canonicalise (c : Char) : Char :=
  match c.toUpper with
  | 'I' => '1'
  | 'L' => '1'
  | 'O' => '0'
  | u => u

def decodeChar (c : Char) : Option Nat := alphabet.findIdx? (· == canonicalise c)

def encode : List UInt8 → List Char
  | [] => []
  | [a] =>
    let n := a.toNat
    [encodeQuintet (n / 8), encodeQuintet (n % 8 * 4)]
  | [a, b] =>
    let n := a.toNat * 256 + b.toNat
    [encodeQuintet (n / 2048), encodeQuintet (n / 64 % 32), encodeQuintet (n / 2 % 32),
      encodeQuintet (n % 2 * 16)]
  | [a, b, c] =>
    let n := a.toNat * 65536 + b.toNat * 256 + c.toNat
    [encodeQuintet (n / 524288), encodeQuintet (n / 16384 % 32), encodeQuintet (n / 512 % 32),
      encodeQuintet (n / 16 % 32), encodeQuintet (n % 16 * 2)]
  | [a, b, c, d] =>
    let n := a.toNat * 16777216 + b.toNat * 65536 + c.toNat * 256 + d.toNat
    [encodeQuintet (n / 134217728), encodeQuintet (n / 4194304 % 32),
      encodeQuintet (n / 131072 % 32), encodeQuintet (n / 4096 % 32),
      encodeQuintet (n / 128 % 32), encodeQuintet (n / 4 % 32), encodeQuintet (n % 4 * 8)]
  | a :: b :: c :: d :: e :: rest =>
    let n := a.toNat * 4294967296 + b.toNat * 16777216 + c.toNat * 65536 + d.toNat * 256 + e.toNat
    encodeQuintet (n / 34359738368) :: encodeQuintet (n / 1073741824 % 32)
      :: encodeQuintet (n / 33554432 % 32) :: encodeQuintet (n / 1048576 % 32)
      :: encodeQuintet (n / 32768 % 32) :: encodeQuintet (n / 1024 % 32)
      :: encodeQuintet (n / 32 % 32) :: encodeQuintet (n % 32) :: encode rest

def oneByte (q0 q1 : Nat) : Option (List UInt8) :=
  if q1 % 4 == 0 then some [UInt8.ofNat (q0 * 8 + q1 / 4)] else none

def twoBytes (q0 q1 q2 q3 : Nat) : Option (List UInt8) :=
  if q3 % 16 == 0 then
    some [UInt8.ofNat (q0 * 8 + q1 / 4), UInt8.ofNat (q1 % 4 * 64 + q2 * 2 + q3 / 16)]
  else none

def threeBytes (q0 q1 q2 q3 q4 : Nat) : Option (List UInt8) :=
  if q4 % 2 == 0 then
    some [UInt8.ofNat (q0 * 8 + q1 / 4), UInt8.ofNat (q1 % 4 * 64 + q2 * 2 + q3 / 16),
      UInt8.ofNat (q3 % 16 * 16 + q4 / 2)]
  else none

def fourBytes (q0 q1 q2 q3 q4 q5 q6 : Nat) : Option (List UInt8) :=
  if q6 % 8 == 0 then
    some [UInt8.ofNat (q0 * 8 + q1 / 4), UInt8.ofNat (q1 % 4 * 64 + q2 * 2 + q3 / 16),
      UInt8.ofNat (q3 % 16 * 16 + q4 / 2), UInt8.ofNat (q4 % 2 * 128 + q5 * 4 + q6 / 8)]
  else none

def fiveBytes (q0 q1 q2 q3 q4 q5 q6 q7 : Nat) : List UInt8 :=
  [UInt8.ofNat (q0 * 8 + q1 / 4), UInt8.ofNat (q1 % 4 * 64 + q2 * 2 + q3 / 16),
    UInt8.ofNat (q3 % 16 * 16 + q4 / 2), UInt8.ofNat (q4 % 2 * 128 + q5 * 4 + q6 / 8),
    UInt8.ofNat (q6 % 8 * 32 + q7)]

def decode : List Char → Option (List UInt8)
  | [] => some []
  | [_] => none
  | [x, y] =>
    match decodeChar x, decodeChar y with
    | some q0, some q1 => oneByte q0 q1
    | _, _ => none
  | [_, _, _] => none
  | [x, y, z, w] =>
    match decodeChar x, decodeChar y, decodeChar z, decodeChar w with
    | some q0, some q1, some q2, some q3 => twoBytes q0 q1 q2 q3
    | _, _, _, _ => none
  | [x, y, z, w, v] =>
    match decodeChar x, decodeChar y, decodeChar z, decodeChar w, decodeChar v with
    | some q0, some q1, some q2, some q3, some q4 => threeBytes q0 q1 q2 q3 q4
    | _, _, _, _, _ => none
  | [_, _, _, _, _, _] => none
  | [x, y, z, w, v, u, t] =>
    match decodeChar x, decodeChar y, decodeChar z, decodeChar w, decodeChar v, decodeChar u,
        decodeChar t with
    | some q0, some q1, some q2, some q3, some q4, some q5, some q6 =>
      fourBytes q0 q1 q2 q3 q4 q5 q6
    | _, _, _, _, _, _, _ => none
  | x :: y :: z :: w :: v :: u :: t :: s :: rest =>
    match decodeChar x, decodeChar y, decodeChar z, decodeChar w, decodeChar v, decodeChar u,
        decodeChar t, decodeChar s, decode rest with
    | some q0, some q1, some q2, some q3, some q4, some q5, some q6, some q7, some tail =>
      some (fiveBytes q0 q1 q2 q3 q4 q5 q6 q7 ++ tail)
    | _, _, _, _, _, _, _, _, _ => none

def encodeString (bytes : List UInt8) : String := String.ofList (encode bytes)

/-- Separators inserted for transcription (AUTH-5.3.2) are ignored, as is surrounding whitespace. -/
def decodeString (s : String) : Option (List UInt8) :=
  decode (s.toList.filter fun c => c != '-' && !c.isWhitespace)

end Authentication.Codec.Base32
