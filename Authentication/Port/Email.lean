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

/-- Chosen from configuration at startup, so a structure rather than a class (AUTH-3.5). -/
structure EmailTransport (m : Type → Type) where
  send : OutboundEmail → m (Except SendError SentMessageId)

end Authentication
