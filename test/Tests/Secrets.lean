/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Tests.Base64Url
import AuthenticationOidc
import Authentication.Instances

/-!
Provider secrets sealed at rest (AUTH-15.7.3.1).

The round trip is the least of it. What the checks are here for is the binding: a ciphertext that
opens under a `SecretRef` other than the one it was sealed under is one tenant reading another's
client secret, and the associated data is the only thing standing in the way.
-/

namespace Tests.Secrets
open Authentication Authentication.Oidc

private def key : SealingKey :=
  { keyId := ⟨"sealing-1"⟩, secret := ⟨List.replicate 32 7 |>.toArray⟩ }

private def otherKey : SealingKey :=
  { keyId := ⟨"sealing-2"⟩, secret := ⟨List.replicate 32 9 |>.toArray⟩ }

private def nonce : ByteArray := ⟨List.replicate 12 3 |>.toArray⟩

private def ring : SealingRing := { current := key }

private def refOf (tenant provider : String) (field : SecretField) : SecretRef :=
  { tenant := ⟨tenant⟩, provider := ⟨provider⟩, field }

/-- A refusal, and the one it was supposed to be. Naming the error matters: an implementation
that refused everything for its own reasons would pass a check that only asked whether it failed. -/
private def failedWith {α : Type} (expected : SecretError) : Except SecretError α → Bool
  | .error actual => actual == expected
  | .ok _ => false

private def alpha : SecretRef := refOf "alpha" "google" .clientSecret

private def plaintext : ByteArray := "a-client-secret".toUTF8

private def opened (r : SecretRef) (sealed : SealedSecret) : IO (Option String) := do
  match ← openSecret ring r sealed with
  | .ok bytes => pure (String.fromUTF8? bytes)
  | .error _ => pure none

def checks : IO (List (String × Bool)) := do
  let sealed ← sealWith key alpha nonce plaintext
  match sealed with
  | .error _ => pure [("secrets: sealing succeeds", false)]
  | .ok sealed =>
    let roundTrip ← opened alpha sealed
    -- The three parts of a `SecretRef` are bound one at a time, because binding two and
    -- forgetting the third is the mistake that would still pass a round-trip check.
    let otherTenant ← opened (refOf "beta" "google" .clientSecret) sealed
    let otherProvider ← opened (refOf "alpha" "apple" .clientSecret) sealed
    let otherField ← opened (refOf "alpha" "google" .signingKey) sealed
    let tampered ← opened alpha { sealed with ciphertext := sealed.ciphertext.push 0 }
    let wrongTag ← opened alpha { sealed with tag := sealed.tag.set! 0 0 }
    let strangeKey ← openSecret ring alpha { sealed with keyId := ⟨"sealing-99"⟩ }
    let shortKey ← sealWith { keyId := ⟨"short"⟩, secret := ⟨#[1, 2, 3]⟩ } alpha nonce plaintext
    let shortNonce ← sealWith key alpha ⟨#[1, 2]⟩ plaintext
    let drawn ← sealSecret key alpha plaintext
    let drawnBack ← match drawn with
      | .ok value => opened alpha value
      | .error _ => pure none
    let external ← (secrets ring).resolve alpha (.external "vault://alpha/google")
    let sealedAgain ← sealWith otherKey alpha nonce plaintext
    let unknownRing ← match sealedAgain with
      | .ok value => openSecret ring alpha value
      | .error _ => pure (.error .undecipherable)
    pure
      [ ("secrets: a sealed secret opens to what was sealed",
          roundTrip == some "a-client-secret")
      , ("secrets: it does not open for another tenant (AUTH-15.7.3.1)", otherTenant.isNone)
      , ("secrets: it does not open for another provider", otherProvider.isNone)
      , ("secrets: it does not open for another field", otherField.isNone)
      , ("secrets: a tampered ciphertext does not open", tampered.isNone)
      , ("secrets: a tampered tag does not open", wrongTag.isNone)
      , ("secrets: a secret sealed under a key the ring lacks reports which key",
          failedWith (.unknownKey ⟨"sealing-99"⟩) strangeKey)
      , ("secrets: a key of the wrong length is refused rather than used",
          failedWith .keyUnusable shortKey)
      , ("secrets: a nonce of the wrong length is refused rather than used",
          failedWith .keyUnusable shortNonce)
      , ("secrets: a drawn nonce round-trips too", drawnBack == some "a-client-secret")
      , ("secrets: an external secret is refused, never guessed at (AUTH-15.7.3)",
          failedWith (.noResolver "vault://alpha/google") external)
      , ("secrets: a secret sealed under a retired key the ring dropped does not open",
          failedWith (.unknownKey ⟨"sealing-2"⟩) unknownRing) ]

/-- Length-prefixing, not a separator. A tenant called `a` with a provider called `b/c` and a
tenant called `a/b` with a provider called `c` join to the same string under any separator that
either may contain, and their associated data must still differ. -/
def associatedDataChecks : List (String × Bool) :=
  [ ("secrets: associated data distinguishes refs a separator would merge",
      associatedData (refOf "a" "b/c" .clientSecret)
        != associatedData (refOf "a/b" "c" .clientSecret))
  , ("secrets: associated data distinguishes the field",
      associatedData (refOf "a" "b" .clientSecret) != associatedData (refOf "a" "b" .signingKey)) ]


/-! ## The written form -/

section Format
open Leancrypto.Codec.Base64Url

/-- A sealed secret sealed, written down, read back and opened. This is the whole of what a
deployment does with one, and until the text form existed it could not be done at all. -/
def formatChecks : IO (List (String × Bool)) := do
  let sealed ← sealWith key alpha nonce plaintext
  match sealed with
  | .error _ => pure [("secrets: sealing succeeds", false)]
  | .ok sealed =>
    let text := (StoredSecret.sealed sealed).render
    let reloaded ← match StoredSecret.parse text with
      | some stored => (secrets ring).resolve alpha stored
      | none => pure (.error .undecipherable)
    let moved ← match StoredSecret.parse text with
      | some stored => (secrets ring).resolve (refOf "beta" "google" .clientSecret) stored
      | none => pure (.error .undecipherable)
    pure
      [ ("secrets: a sealed secret survives being written down and read back",
          reloaded.toOption.bind String.fromUTF8? == some "a-client-secret")
      , ("secrets: the text carries the binding with it, so it still opens for nobody else",
          failedWith .undecipherable moved)
      , ("secrets: a reference with dots in it comes back whole",
          StoredSecret.parse (StoredSecret.external "vault://acme.example.com/google").render
            == some (.external "vault://acme.example.com/google"))
      , ("secrets: text of another shape is refused rather than guessed at",
          ["", "v1", "v1.s", "v1.s.a.b.c", "v2.s.a.b.c.d", "v1.s.!.b.c.d"].all
            (StoredSecret.parse · |>.isNone)) ]

/-- No character outside the base64url alphabet occurs in its output, and the dot is outside it.
That is what lets the separator separate: a field able to hold one would be read as two, and the
fields here are a tenant's client secret. -/
private theorem dot_not_mem_encodeString (bytes : ByteArray) :
    '.' ∉ (encodeString bytes).toList :=
  Tests.Base64Url.notMem_encodeString (by decide) (by decide) bytes

/--
The five separators the writer put in are the only five there, so splitting the text finds exactly
the six fields it wrote. Everything else about the format rests on this: a field read as two, or
two read as one, is a secret that opens as something else or not at all.

`k`, `n`, `c` and `t` are arbitrary byte arrays standing for the four fields, so the claim is about
every sealed secret rather than any particular one. The left side is the rendered text as a
character list, dots and all, and the right side names the six fields the reader should find. It
follows from `splitOn` being the inverse of joining with a separator, whose side condition is that
no field contains one, which the theorem above supplies for the four encoded fields and `decide`
for the two literals.
-/
private theorem split_fields (k n c t : ByteArray) :
    List.splitOn '.' ('v' :: '1' :: '.' :: 's' :: '.' ::
        ((encodeString k).toList ++ '.' :: ((encodeString n).toList ++ '.' ::
          ((encodeString c).toList ++ '.' :: (encodeString t).toList))))
      = [['v', '1'], ['s'], (encodeString k).toList, (encodeString n).toList,
          (encodeString c).toList, (encodeString t).toList] := by
  have parts : ∀ l ∈ [['v', '1'], ['s'], (encodeString k).toList, (encodeString n).toList,
      (encodeString c).toList, (encodeString t).toList], '.' ∉ l := by
    simp [dot_not_mem_encodeString]
  have shape : ('v' :: '1' :: '.' :: 's' :: '.' ::
      ((encodeString k).toList ++ '.' :: ((encodeString n).toList ++ '.' ::
        ((encodeString c).toList ++ '.' :: (encodeString t).toList))))
      = ['.'].intercalate [['v', '1'], ['s'], (encodeString k).toList, (encodeString n).toList,
          (encodeString c).toList, (encodeString t).toList] := by
    simp [List.intercalate]
  rw [shape, List.splitOn_intercalate '.' parts (by simp)]

/--
A sealed secret written down and read back is the same sealed secret, whatever is in it. This is
a theorem rather than a handful of examples because the format is one a deployment's configuration
is written in and this library has to keep reading: a value that came back subtly different would
not be a parse error but a sign-in that fails under a key nobody can find.

`value` is any sealed secret at all, so the claim covers every key identifier, nonce, ciphertext
and tag rather than the ones an example would pick. `codec` is `leancrypto`'s base64url round trip:
it is proved in that library's own suite but not exported from it, and proving it again here would
be this suite testing a dependency. The key identifier makes the further trip through UTF-8, whose
round trip is discharged from the fact that a `String`'s bytes are valid UTF-8 by construction.
-/
theorem parse_render_sealed (value : SealedSecret)
    (codec : ∀ b : ByteArray, decodeString (encodeString b) = some b) :
    StoredSecret.parse (StoredSecret.render (.sealed value)) = some (.sealed value) := by
  have hu : String.fromUTF8? value.keyId.value.toByteArray = some value.keyId.value := by
    simp [String.fromUTF8?, String.fromUTF8, value.keyId.value.isValidUTF8]
  simp [StoredSecret.parse, StoredSecret.render, String.toList_append, split_fields, codec, hu]

/--
The same for the other kind of stored secret. A reference is the client's own text and this
library knows nothing about its shape, so the one thing it owes whoever wrote it is to hand back
what was written.

`reference` is any string, dots and all, which is the case worth stating: the reference is the
remainder of the text rather than a field, so nothing in it needs escaping and nothing in it can
be mistaken for the end. Unlike the sealed case this rests on no encoding at all, which is why it
needs no hypothesis.
-/
theorem parse_render_external (reference : String) :
    StoredSecret.parse (StoredSecret.render (.external reference))
      = some (.external reference) := by
  simp [StoredSecret.parse, StoredSecret.render, String.toList_append]

end Format

end Tests.Secrets
