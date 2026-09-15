/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import AuthSeal
import Authentication.Instances

/-!
The sealing tool (§21).

Every decision it makes is a function, so none of this needs a shell (AUTH-21.6.2). What is worth
checking is what the tool exists to say: that a secret sealed against the wrong tenant, provider
or field does not open, and that the refusal names what to change.
-/

namespace Tests.Seal
open Authentication Authentication.Oidc AuthSeal

private def secret : ByteArray := ⟨List.replicate 32 5 |>.toArray⟩

private def key : SealingKey := { keyId := ⟨"sealing-2026-01"⟩, secret }

private def refOf (tenant provider : String) (field : SecretField) : SecretRef :=
  { tenant := ⟨tenant⟩, provider := ⟨provider⟩, field }

private def acme : SecretRef := refOf "acme" "google" .clientSecret

private def plaintext : String := "the-secret-google-gave-you"

private def contains (needle haystack : String) : Bool := (haystack.splitOn needle).length > 1

private def refused {α : Type} : Except String α → Bool
  | .error _ => true
  | .ok _ => false

/-- A refusal that names neither the variable nor the argument to change leaves whoever ran it
where they started (AUTH-21.4.1). -/
private def refusedNaming {α : Type} (name : String) : Except String α → Bool
  | .error message => contains name message
  | .ok _ => false

private def parsesTo (args : List String) (command : Command) : Bool :=
  match parseCommand args with
  | .ok actual => decide (actual = command)
  | .error _ => false

def parsingChecks : List (String × Bool) :=
  [ ("seal: the three verbs parse", #[
        parsesTo ["key"] .mint,
        parsesTo ["seal", "acme", "google", "client-secret", "k"] (.seal acme ⟨"k"⟩),
        parsesTo ["check", "acme", "google", "signing-key", "k"]
          (.check (refOf "acme" "google" .signingKey) ⟨"k"⟩)].all id)
  , ("seal: a field name nothing answers to is refused, and the names are offered",
      refusedNaming "client-secret"
        (parseCommand ["seal", "acme", "google", "clientSecret", "k"]))
  , ("seal: nothing is defaulted, so a missing argument is a refusal (AUTH-21.2.4)",
      #[ parseCommand ["seal", "acme", "google", "client-secret"],
         parseCommand ["check", "acme", "google"],
         parseCommand ["seal"],
         parseCommand [] ].all refused)
  , ("seal: a verb nothing answers to is refused", refused (parseCommand ["open", "acme"])) ]

/-- A key of any other length is refused rather than made to fit, because every way of making it
fit seals secrets under a key nobody wrote down (AUTH-21.4.4). -/
def keyChecks : List (String × Bool) :=
  let encoded := Leancrypto.Codec.Base64Url.encodeString secret
  [ ("seal: a key of the cipher's own length is accepted", (decodeKey encoded).isOk)
  , ("seal: surrounding whitespace is not part of the key", (decodeKey s!"  {encoded}\n").isOk)
  , ("seal: a key that is not base64url is refused, naming the variable",
      refusedNaming keyVariable (decodeKey "not base64url!"))
  , ("seal: a short key is refused rather than padded",
      refusedNaming keyVariable
        (decodeKey (Leancrypto.Codec.Base64Url.encodeString ⟨#[1, 2, 3]⟩)))
  , ("seal: a long key is refused rather than truncated",
      refusedNaming keyVariable
        (decodeKey (Leancrypto.Codec.Base64Url.encodeString (secret.push 0)))) ]

def mintChecks : IO (List (String × Bool)) := do
  let minted ← mintKey
  pure
    [ ("seal: a minted key is one the tool itself accepts (AUTH-21.2.1)",
        match minted with
        | .ok text => (decodeKey text).isOk
        | .error _ => false) ]

def sealChecks : IO (List (String × Bool)) := do
  let sealed ← sealText key acme plaintext.toUTF8
  match sealed with
  | .error _ => pure [("seal: sealing succeeds", false)]
  | .ok text =>
    let opens ← checkText key acme text
    let newline ← checkText key acme (text ++ "\n")
    let otherTenant ← checkText key (refOf "beta" "google" .clientSecret) text
    let otherProvider ← checkText key (refOf "acme" "apple" .clientSecret) text
    let otherField ← checkText key (refOf "acme" "google" .signingKey) text
    let otherKey ← checkText { key with secret := ⟨List.replicate 32 9 |>.toArray⟩ } acme text
    let otherKeyId ← checkText { key with keyId := ⟨"sealing-2026-06"⟩ } acme text
    let external ← checkText key acme (StoredSecret.render (.external "vault://acme/google"))
    let nonsense ← checkText key acme "not a stored secret"
    let empty ← sealText key acme .empty
    pure
      [ ("seal: what the tool sealed is what the tool opens", opens.isOk)
      , ("seal: the newline a shell adds is not part of the value", newline.isOk)
      , ("seal: it does not open for another tenant (AUTH-15.7.3.1)",
          refusedNaming "<tenant>" otherTenant)
      , ("seal: it does not open for another provider", refusedNaming "<provider>" otherProvider)
      , ("seal: it does not open for another field", refusedNaming "<field>" otherField)
      , ("seal: it does not open under another key, naming the variable to change",
          refusedNaming keyVariable otherKey)
      -- The wrong key and the wrong reference are the same refusal, and that is the point of it
      -- (AUTH-21.4.3).
      , ("seal: the wrong key and the wrong reference are not told apart",
          match otherKey, otherTenant with
          | .error left, .error right => left == right
          | _, _ => false)
      , ("seal: a key id the value was not sealed under is a refusal of its own (AUTH-21.4.2)",
          refusedNaming "<key-id>" otherKeyId)
      , ("seal: a check reports both key identifiers, so an outstanding reseal shows (AUTH-21.5.2)",
          match otherKeyId with
          | .error message =>
            contains "sealing-2026-01" message && contains "sealing-2026-06" message
          | .ok _ => false)
      , ("seal: an external reference is reported as nothing to open", refused external)
      , ("seal: text of another shape is refused rather than guessed at", refused nonsense)
      , ("seal: nothing on standard input seals nothing", refused empty)
      -- Whoever ran this is diagnosing a live deployment, and the one thing they must not be
      -- handed is the secret itself (AUTH-21.2.3).
      , ("seal: nothing the tool prints is what the value opens to",
          #[opens, otherTenant, otherKeyId, external, nonsense].all fun outcome =>
            match outcome with
            | .ok message | .error message => !contains plaintext message) ]

end Tests.Seal
