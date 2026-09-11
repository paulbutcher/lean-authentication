/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
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

end Tests.Secrets
