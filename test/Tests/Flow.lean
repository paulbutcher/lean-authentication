/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Authentication.Attempt

/-!
The cross-device flow driven end to end through the pure layer, and the adversarial cases of
AUTH-16.7 that do not need a store.

The theorems in the sibling modules say what `step` can never do. These say what it does for
one worked flow, which is what catches an effect list that is right in every case the theorems
constrain and empty in the case they do not.
-/

namespace Tests.Flow
open Authentication Authentication.Attempt

def tenant : TenantId := ⟨"acme"⟩

def addressOrDefault (raw : String) : EmailAddress :=
  (EmailAddress.parse raw).toOption.getD default

def config : TenantConfig tenant :=
  { displayName := "Acme"
    baseUrl := ⟨"https://auth.example.com"⟩
    sendingIdentity :=
      { address := addressOrDefault "sign-in@auth.example.com", displayName := "Acme sign-in" }
    signupPolicy := .unrestricted }

def key : KeyId := ⟨"pepper-1"⟩

def minted (value : String) (bytes : List UInt8) : MintedCredential := ⟨⟨value⟩, ⟨key, bytes⟩⟩

def presenting (bytes : List UInt8) : PresentedSecret := ⟨[⟨key, bytes⟩]⟩

def tokenBytes : List UInt8 := [17, 42, 99, 3]
def codeBytes : List UInt8 := [7, 7, 1]
def nonceBytes : List UInt8 := [200, 13]

def secrets : MintedSecrets :=
  { magicToken := minted "Wm9uZQ" tokenBytes
    revealedCode := minted "4RTG-9KPZ" codeBytes
    emailedCode := none
    bindingNonce := minted "bm9uY2U" nonceBytes }

def now : Timestamp := ⟨1700000000⟩
def afterExpiry : Timestamp := ⟨1700009999⟩

def attemptId : AttemptId tenant := ⟨"attempt-1"⟩

def started : AttemptState tenant × List (Effect tenant) :=
  begin config now attemptId (addressOrDefault "person@example.com") secrets {}

abbrev Outcome := Except AuthError (AttemptState tenant × List (Effect tenant))

def phaseOf (result : Outcome) : Option AttemptPhase := result.toOption.map (·.1.phase)

def errorOf (result : Outcome) : Option AuthError :=
  match result with
  | .error e => some e
  | .ok _ => none

def isSession : Effect tenant → Bool
  | .issueSession _ => true
  | _ => false

def isMail : Effect tenant → Bool
  | .sendSignInEmail _ => true
  | _ => false

def isCookie : Effect tenant → Bool
  | .setAttemptCookie _ => true
  | _ => false

def views (result : Outcome) : List View :=
  (result.toOption.map (·.2.filterMap fun e =>
    match e with
    | .present view => some view
    | _ => none)).getD []

def issuesSession (result : Outcome) : Bool := (result.toOption.map (·.2.any isSession)).getD false

def cookie : PresentedSecret := presenting nonceBytes
def token : PresentedSecret := presenting tokenBytes
def code : PresentedSecret := presenting codeBytes
def wrongCode : PresentedSecret := presenting [0, 0, 0]

def openedCrossDevice : Outcome := step config now started.1 (.linkOpened token none)
def openedSameDevice : Outcome := step config now started.1 (.linkOpened token (some cookie))

def revealed : AttemptState tenant :=
  (openedCrossDevice.toOption.map (·.1)).getD started.1

/-- Applies `count` wrong codes in succession, so the entry budget is reached the way a guesser
would reach it. -/
def afterWrongCodes (count : Nat) (state : AttemptState tenant) : Outcome :=
  match count with
  | 0 => .ok (state, [])
  | n + 1 =>
    match step config now state (.revealedCodeSubmitted cookie wrongCode) with
    | .ok (next, _) => afterWrongCodes n next
    | .error e => .error e

def exhausted : AttemptState tenant := ((afterWrongCodes 5 revealed).toOption.map (·.1)).getD revealed

def expiredAttempt : AttemptState tenant := { revealed with expiresAt := ⟨1700000060⟩ }

def checks : List (String × Bool) :=
  [ ("sign-in mail is sent when an attempt begins", started.2.any isMail),
    ("the attempt cookie is set when an attempt begins", started.2.any isCookie),
    ("a new attempt is pending", started.1.phase == .pending),
    ("no session is issued when an attempt begins", !started.2.any isSession),
    ("opening the link reveals the attempt", phaseOf openedCrossDevice == some .revealed),
    ("a link opened cross-device shows the code", views openedCrossDevice == [.showVerificationCode]),
    ("a link opened cross-device issues no session", !issuesSession openedCrossDevice),
    ("a link opened same-device offers the button", views openedSameDevice == [.confirmSignIn]),
    ("a link opened same-device issues no session", !issuesSession openedSameDevice),
    ("opening the link twice is idempotent",
      phaseOf (step config now revealed (.linkOpened token none)) == some .revealed),
    ("the wrong token is refused",
      errorOf (step config now started.1 (.linkOpened wrongCode none)) == some .unknownToken),
    ("the code completes the attempt",
      phaseOf (step config now revealed (.revealedCodeSubmitted cookie code)) == some .completed),
    ("completing the attempt issues a session",
      issuesSession (step config now revealed (.revealedCodeSubmitted cookie code))),
    ("the code is refused without the attempt cookie",
      errorOf (step config now revealed (.revealedCodeSubmitted (presenting [1]) code))
        == some .notOriginatingBrowser),
    ("the button is refused without the attempt cookie",
      errorOf (step config now revealed (.completionRequested (presenting [1])))
        == some .notOriginatingBrowser),
    ("five wrong codes leave the attempt alive", (afterWrongCodes 5 revealed).toOption.isSome),
    ("five wrong codes are counted", exhausted.failedCodeEntries == 5),
    ("five wrong codes leave the attempt revealed", exhausted.phase == .revealed),
    ("the sixth entry abandons the attempt",
      phaseOf (step config now exhausted (.revealedCodeSubmitted cookie wrongCode))
        == some .abandoned),
    ("a correct code as the sixth entry abandons the attempt too",
      phaseOf (step config now exhausted (.revealedCodeSubmitted cookie code)) == some .abandoned),
    ("an abandoned attempt refuses the magic token",
      errorOf (step config now { exhausted with phase := .abandoned } (.linkOpened token (some cookie)))
        == some .attemptNotLive),
    ("an expired attempt refuses a correct code",
      errorOf (step config afterExpiry expiredAttempt (.revealedCodeSubmitted cookie code))
        == some .attemptExpired),
    ("an expired attempt refuses the button",
      errorOf (step config afterExpiry expiredAttempt (.completionRequested cookie))
        == some .attemptExpired),
    ("a superseded attempt is abandoned",
      phaseOf (step config now revealed .superseded) == some .abandoned),
    ("the emailed code is refused unless the tenant enabled it",
      errorOf (step config now revealed (.emailedCodeSubmitted cookie code))
        == some .emailedCodeNotEnabled),
    ("an address round-trips through parsing",
      (EmailAddress.parse "person@example.com").toOption.isSome) ]

end Tests.Flow
