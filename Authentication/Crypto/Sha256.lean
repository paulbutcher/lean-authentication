/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
SHA-256 (FIPS 180-4).

Written against the published test vectors rather than proved: the round function is
arithmetic on machine words with no structure a proof could exploit, and a golden vector
catches every transcription error the code can contain.
-/

namespace Authentication.Crypto.Sha256

private def roundConstants : Array UInt32 :=
  #[0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
    0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
    0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
    0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
    0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
    0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
    0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
    0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2]

private def initialState : Array UInt32 :=
  #[0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19]

/-- Rotation counts in SHA-256 are always between 1 and 31, so the complementary shift is never
a whole word. -/
private def rotr (x : UInt32) (n : UInt32) : UInt32 := (x >>> n) ||| (x <<< (32 - n))

private def word (bytes : Array UInt8) (offset : Nat) : UInt32 :=
  ((bytes.getD offset 0).toUInt32 <<< 24) ||| ((bytes.getD (offset + 1) 0).toUInt32 <<< 16) |||
    ((bytes.getD (offset + 2) 0).toUInt32 <<< 8) ||| (bytes.getD (offset + 3) 0).toUInt32

/-- Appends the terminator, the zero fill, and the message length in bits as a big-endian
64-bit count. -/
private def pad (message : Array UInt8) : Array UInt8 := Id.run do
  let bitLength : UInt64 := (UInt64.ofNat message.size) * 8
  let afterTerminator := message.size + 1
  let zeros := (56 + 64 - afterTerminator % 64) % 64
  let mut padded := message.push 0x80
  for _ in [0:zeros] do
    padded := padded.push 0
  for shift in [0:8] do
    padded := padded.push (bitLength >>> (UInt64.ofNat ((7 - shift) * 8))).toUInt8
  pure padded

private def schedule (chunk : Array UInt8) : Array UInt32 := Id.run do
  let mut w : Array UInt32 := Array.emptyWithCapacity 64
  for i in [0:16] do
    w := w.push (word chunk (i * 4))
  for i in [16:64] do
    let previous := w.getD (i - 15) 0
    let recent := w.getD (i - 2) 0
    let s0 := rotr previous 7 ^^^ rotr previous 18 ^^^ (previous >>> 3)
    let s1 := rotr recent 17 ^^^ rotr recent 19 ^^^ (recent >>> 10)
    w := w.push (w.getD (i - 16) 0 + s0 + w.getD (i - 7) 0 + s1)
  pure w

private def compress (state : Array UInt32) (chunk : Array UInt8) : Array UInt32 := Id.run do
  let w := schedule chunk
  let mut a := state.getD 0 0
  let mut b := state.getD 1 0
  let mut c := state.getD 2 0
  let mut d := state.getD 3 0
  let mut e := state.getD 4 0
  let mut f := state.getD 5 0
  let mut g := state.getD 6 0
  let mut h := state.getD 7 0
  for i in [0:64] do
    let s1 := rotr e 6 ^^^ rotr e 11 ^^^ rotr e 25
    let choice := (e &&& f) ^^^ ((~~~e) &&& g)
    let temp1 := h + s1 + choice + roundConstants.getD i 0 + w.getD i 0
    let s0 := rotr a 2 ^^^ rotr a 13 ^^^ rotr a 22
    let majority := (a &&& b) ^^^ (a &&& c) ^^^ (b &&& c)
    let temp2 := s0 + majority
    h := g; g := f; f := e; e := d + temp1
    d := c; c := b; b := a; a := temp1 + temp2
  pure #[state.getD 0 0 + a, state.getD 1 0 + b, state.getD 2 0 + c, state.getD 3 0 + d,
    state.getD 4 0 + e, state.getD 5 0 + f, state.getD 6 0 + g, state.getD 7 0 + h]

def hashArray (message : Array UInt8) : Array UInt8 := Id.run do
  let padded := pad message
  let mut state := initialState
  for chunk in [0:padded.size / 64] do
    state := compress state (padded.extract (chunk * 64) (chunk * 64 + 64))
  let mut digest : Array UInt8 := Array.emptyWithCapacity 32
  for value in state do
    for shift in [0:4] do
      digest := digest.push (value >>> (UInt32.ofNat ((3 - shift) * 8))).toUInt8
  pure digest

def hash (message : List UInt8) : List UInt8 := (hashArray message.toArray).toList

def hashString (message : String) : List UInt8 := (hashArray message.toUTF8.toList.toArray).toList

end Authentication.Crypto.Sha256
