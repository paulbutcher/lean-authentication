/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
Base64url (RFC 4648 §5) without padding.

Bits beyond the encoded bytes are required to be zero, so a byte string has exactly one
accepted encoding. Without that check a credential would have several spellings, and a store
keyed on the digest of the spelling would treat them as different credentials.
-/

namespace Authentication.Codec.Base64Url

def alphabet : List Char :=
  "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789-_".toList

def encodeSextet (n : Nat) : Char := alphabet.getD n '='

def decodeChar (c : Char) : Option Nat := alphabet.findIdx? (· == c)

def encode : List UInt8 → List Char
  | [] => []
  | [a] =>
    let n := a.toNat
    [encodeSextet (n / 4), encodeSextet (n % 4 * 16)]
  | [a, b] =>
    let n := a.toNat * 256 + b.toNat
    [encodeSextet (n / 1024), encodeSextet (n / 16 % 64), encodeSextet (n % 16 * 4)]
  | a :: b :: c :: rest =>
    let n := a.toNat * 65536 + b.toNat * 256 + c.toNat
    encodeSextet (n / 262144) :: encodeSextet (n / 4096 % 64) :: encodeSextet (n / 64 % 64)
      :: encodeSextet (n % 64) :: encode rest

def oneByte (s0 s1 : Nat) : Option (List UInt8) :=
  if s1 % 16 == 0 then some [UInt8.ofNat (s0 * 4 + s1 / 16)] else none

def twoBytes (s0 s1 s2 : Nat) : Option (List UInt8) :=
  if s2 % 4 == 0 then
    some [UInt8.ofNat (s0 * 4 + s1 / 16), UInt8.ofNat (s1 % 16 * 16 + s2 / 4)]
  else none

def threeBytes (s0 s1 s2 s3 : Nat) : List UInt8 :=
  [UInt8.ofNat (s0 * 4 + s1 / 16), UInt8.ofNat (s1 % 16 * 16 + s2 / 4),
    UInt8.ofNat (s2 % 4 * 64 + s3)]

def decode : List Char → Option (List UInt8)
  | [] => some []
  | [_] => none
  | [x, y] =>
    match decodeChar x, decodeChar y with
    | some s0, some s1 => oneByte s0 s1
    | _, _ => none
  | [x, y, z] =>
    match decodeChar x, decodeChar y, decodeChar z with
    | some s0, some s1, some s2 => twoBytes s0 s1 s2
    | _, _, _ => none
  | x :: y :: z :: w :: rest =>
    match decodeChar x, decodeChar y, decodeChar z, decodeChar w, decode rest with
    | some s0, some s1, some s2, some s3, some tail => some (threeBytes s0 s1 s2 s3 ++ tail)
    | _, _, _, _, _ => none

def encodeString (bytes : List UInt8) : String := String.ofList (encode bytes)

def decodeString (s : String) : Option (List UInt8) := decode s.toList

end Authentication.Codec.Base64Url
