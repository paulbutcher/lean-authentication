/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import AuthenticationOidc

/-!
The sealing tool (§21): mint a sealing key, seal a provider secret under a `SecretRef`, and say
whether a configured value still opens under the key held.

Every decision is a function here rather than in `main`, so the parsing, the binding and the
refusals are exercised in process (AUTH-21.6.2). Nothing here writes a file, and nothing prints
what a value opens to.
-/

public section

namespace AuthSeal

open Authentication Authentication.Oidc

-- The key is written in base64url, because the stored form's own fields are (AUTH-15.7.3.2).
open Leancrypto.Codec.Base64Url

/-- The sealing key arrives in the environment rather than as an argument, which would be in the
process list while the tool runs and in a shell history afterwards. -/
def keyVariable : String := "AUTH_SEALING_KEY"

inductive Command where
  | mint
  | seal (ref : SecretRef) (keyId : KeyId)
  | check (ref : SecretRef) (keyId : KeyId)
  deriving DecidableEq, Repr

def fieldNames : String := String.intercalate ", " (SecretField.all.map SecretField.name)

def usage : String :=
  "usage:\n" ++
  "  auth-seal key\n" ++
  "  auth-seal seal <tenant> <provider> <field> <key-id>   < the secret\n" ++
  "  auth-seal check <tenant> <provider> <field> <key-id>  < the configured value\n\n" ++
  s!"<field> is one of {fieldNames}. seal and check read {keyVariable} from the environment; " ++
  "key mints one to put there.\n" ++
  "seal reads the secret from standard input as bytes, and check the text a deployment holds."

private def refOf (tenant provider : String) (field : SecretField) : SecretRef :=
  { tenant := ⟨tenant⟩, provider := ⟨provider⟩, field }

/-- The tenant and the provider are taken as given: which providers exist is a client's
configuration, so checking them against a list here would refuse one the library supports. -/
def parseCommand : List String → Except String Command
  | ["key"] => .ok .mint
  | ["seal", tenant, provider, field, keyId] =>
    (parseField field).map fun field => .seal (refOf tenant provider field) ⟨keyId⟩
  | ["check", tenant, provider, field, keyId] =>
    (parseField field).map fun field => .check (refOf tenant provider field) ⟨keyId⟩
  | _ => .error usage
where
  parseField (text : String) : Except String SecretField :=
    match SecretField.parse text with
    | some field => .ok field
    | none => .error s!"<field> is {text}, which names no secret field. It is one of {fieldNames}."

def decodeKey (text : String) : Except String ByteArray :=
  match decodeString text.trimAscii.toString with
  | none => .error s!"{keyVariable} is not base64url. Mint one with `auth-seal key`."
  | some secret =>
    if secret.size == algorithm.keyLength then .ok secret
    else .error s!"{keyVariable} decodes to {secret.size} bytes, and the cipher takes \
      {algorithm.keyLength}. Mint one with `auth-seal key`."

/-- Exhaustive rather than defaulted, so that a case added to `SecretError` does not compile until
this has an answer for it (AUTH-21.4.2). -/
def explain : SecretError → String
  | .unknownKey keyId =>
    s!"does not open: it is sealed under key id {keyId.value}, which is not the <key-id> given. \
      Run this again under that key id, or reseal the secret under the one you gave."
  | .undecipherable =>
    s!"does not open: either {keyVariable} is not the key it was sealed under, or <tenant>, \
      <provider> and <field> are not the ones it was sealed against. Which of the two it is, \
      this does not say."
  | .keyUnusable =>
    s!"{keyVariable} is not the length the cipher takes. Mint one with `auth-seal key`."
  | .noNonce detail => s!"the random source would not answer, so nothing was sealed: {detail}"
  | .noResolver reference =>
    s!"nothing to open: the value names an external secret ({reference}), which is resolved by \
      the deployment's own `Secrets` port and not by anything here."

/-- The key identifier a value carries beside the one held, which is the comparison that says
whether a reseal is still outstanding (AUTH-21.5.2). -/
def keyIds (stored : StoredSecret) (held : KeyId) : String :=
  match stored with
  | .sealed value => s!"sealed under key id {value.keyId.value}, key id held {held.value}"
  | .external reference => s!"an external reference ({reference}), key id held {held.value}"

def mintKey [RandomBytes IO] : IO (Except String String) := do
  match ← RandomBytes.draw algorithm.keyLength with
  | .error detail =>
    pure (.error s!"the random source would not answer, so no key was minted: {detail}")
  | .ok secret => pure (.ok (encodeString secret))

/-- An empty secret is refused rather than sealed, because the only way to arrive with one is to
have piped in nothing. -/
def sealText [RandomBytes IO] (key : SealingKey) (ref : SecretRef) (plaintext : ByteArray) :
    IO (Except String String) := do
  if plaintext.isEmpty then
    return .error "nothing arrived on standard input, so there is no secret to seal."
  match ← sealSecret key ref plaintext with
  | .error error => pure (.error (explain error))
  | .ok value => pure (.ok (StoredSecret.sealed value).render)

/-- Says whether the value opens and never what it opens to, so that this is safe to run against
the configuration of a running deployment (AUTH-21.2.3). -/
def checkText (key : SealingKey) (ref : SecretRef) (text : String) : IO (Except String String) := do
  match StoredSecret.parse text.trimAscii.toString with
  | none => pure (.error "does not open: the value is not in the form `auth-seal seal` writes.")
  | some stored =>
    let ids := keyIds stored key.keyId
    match ← (secrets { current := key }).resolve ref stored with
    | .ok _ => pure (.ok s!"opens, {ids}")
    | .error error => pure (.error s!"{explain error}\n{ids}")

private def sealingKey (keyId : KeyId) : IO (Except String SealingKey) := do
  match ← IO.getEnv keyVariable with
  | none => pure (.error s!"{keyVariable} is not set. Mint a key with `auth-seal key`.")
  | some text => pure ((decodeKey text).map fun secret => { keyId, secret })

/-- The secret is read as bytes and never as a string, so that an Apple `.p8` is sealed as the
file's own bytes whatever they encode. The value a check reads is text a deployment typed, so a
trailing newline from the shell is not part of it. -/
def run [RandomBytes IO] : Command → IO (Except String String)
  | .mint => mintKey
  | .seal ref keyId => do
    match ← sealingKey keyId with
    | .error message => pure (.error message)
    | .ok key => sealText key ref (← (← IO.getStdin).readBinToEnd)
  | .check ref keyId => do
    match ← sealingKey keyId with
    | .error message => pure (.error message)
    | .ok key =>
      match String.fromUTF8? (← (← IO.getStdin).readBinToEnd) with
      | none => pure (.error "the value on standard input is not text.")
      | some text => checkText key ref text

end AuthSeal
