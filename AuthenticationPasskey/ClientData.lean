/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import AuthenticationPasskey.Error
public import Authentication
public import Json

/-!
`clientDataJSON`, which the browser writes and the authenticator signs over without reading.

What matters is that the three fields are compared rather than merely parsed: the type, so a
registration challenge cannot complete an assertion; the challenge, so an assertion cannot be
replayed; and the origin, which is the one the browser knows and the page cannot lie about.
-/

public section

namespace Authentication.Passkey

/-- Which ceremony a `clientDataJSON` says it belongs to. These are the exact strings WebAuthn
fixes, and they are compared rather than interpreted. -/
def registrationType : String := "webauthn.create"
def assertionType : String := "webauthn.get"

def clientDataType : PasskeyCeremonyKind → String
  | .registration => registrationType
  | .authentication => assertionType

/-- What the three checked members said, once each has been found and is of the right type. -/
structure ClientData where
  type : String
  /-- Base64url as the browser wrote it, which is the form it is compared in: decoding first
  would make two spellings of one challenge compare equal. -/
  challenge : String
  origin : String
  crossOrigin : Bool
  deriving DecidableEq, Repr, Inhabited

namespace ClientData

private def stringMember (value : Json) (name : String) : Except PasskeyError String :=
  match (value.getObjVal? name).toOption.bind (·.getStr?.toOption) with
  | some text => .ok text
  | none => .error (.badClientData name)

/-- Absent means `false`, which is what WebAuthn says, and a present member of the wrong type is
a refusal rather than a default: a browser that disagrees about the shape of this object is not
one to guess on behalf of. -/
private def crossOriginMember (value : Json) : Except PasskeyError Bool :=
  match (value.getObjVal? "crossOrigin").toOption with
  | none => .ok false
  | some member =>
    match member.getBool?.toOption with
    | some flag => .ok flag
    | none => .error (.badClientData "crossOrigin")

def parse (text : String) : Except PasskeyError ClientData :=
  match Json.parse text with
  | .error _ => .error (.badClientData "")
  | .ok value => do
    pure
      { type := ← stringMember value "type"
        challenge := ← stringMember value "challenge"
        origin := ← stringMember value "origin"
        crossOrigin := ← crossOriginMember value }

/--
Whether this client data belongs to the ceremony that was begun.

`challengeAccepts` decides the challenge and `origins` are the origins this tenant answers on. The
challenge arrives as a predicate rather than as a value because a ceremony record holds only its
digest: digesting the echoed value needs the pepper, which lives at the edge, so the edge supplies
the comparison and nothing here can be given the challenge in clear. Taking it as an argument also
means this cannot return without having asked.
-/
def check (data : ClientData) (kind : PasskeyCeremonyKind) (challengeAccepts : String → Bool)
    (origins : List String) : Except PasskeyError Unit := do
  if data.type != clientDataType kind then .error .wrongCeremonyType
  else if !challengeAccepts data.challenge then .error .challengeMismatch
  else if !origins.contains data.origin then .error .originNotAllowed
  else if data.crossOrigin then .error .crossOrigin
  else .ok ()

end ClientData

end Authentication.Passkey
