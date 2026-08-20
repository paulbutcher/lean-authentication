/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Authentication.Config
import Authentication.Email

public section

namespace Authentication

/--
Permanent and transient failures are distinguished because the caller's response differs: one
is told to the person, the other is retried (AUTH-10.3).
-/
inductive SendError where
  | addressRejected (detail : String)
  | addressSuppressed
  | rateLimited
  | timedOut
  | providerFailure (detail : String)
  deriving DecidableEq, Repr, Inhabited

namespace SendError

def isPermanent : SendError → Bool
  | .addressRejected _ | .addressSuppressed => true
  | .rateLimited | .timedOut | .providerFailure _ => false

end SendError

structure SentMessageId where
  value : String
  deriving DecidableEq, Repr, Inhabited

structure OutboundEmail where
  «from» : SendingIdentity
  to : EmailAddress
  subject : String
  textBody : String
  htmlBody : Option String := none
  replyTo : Option EmailAddress := none
  headers : List (String × String) := []
  /-- Derived from the attempt, so a retry after an ambiguous timeout cannot put two codes in
  front of one person (AUTH-10.4). -/
  idempotencyKey : String
  deriving DecidableEq, Repr, Inhabited

namespace OutboundEmail

/-- Enough of the message to sign in by reading it. The text body is reproduced whole because it
is what carries the link and the code, and nothing else does. -/
def render (mail : OutboundEmail) : String :=
  String.intercalate "\n"
    [ "-- email --"
    , "To: " ++ mail.to.render
    , "Subject: " ++ mail.subject
    , ""
    , mail.textBody
    , "-- end --" ]

end OutboundEmail

/-- Chosen from configuration at startup, so a structure rather than a class (AUTH-3.5). -/
structure EmailTransport (m : Type → Type) where
  send : OutboundEmail → m (Except SendError SentMessageId)

namespace EmailTransport

/--
Hands each message to `sink` and reports success rather than sending it. Every provider
integration needs an account and credentials, which a developer running the application locally
has not got, and the magic link exists nowhere but inside the message; this is what lets them
sign in anyway.

The reported id is the message's own idempotency key rather than an invented one, so a caller
keying anything off it sees the value a real transport would return for the same message.

For development only. The message carries the sign-in credential in the clear, so whoever can
read wherever `sink` writes can sign in as whoever asked to.
-/
def capturing {m : Type → Type} [Monad m] (sink : OutboundEmail → m Unit) :
    EmailTransport m where
  send mail := do
    sink mail
    pure (.ok ⟨mail.idempotencyKey⟩)

/-- `capturing` with the sink already chosen, which is the wiring a local `main` wants. It prints
sign-in links and codes to the console, so everything `capturing` says applies with the sink
named: development only, and whoever reads the console can sign in as anyone. -/
def console : EmailTransport IO := capturing fun mail => IO.println mail.render

end EmailTransport

end Authentication
