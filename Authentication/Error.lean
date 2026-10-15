/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public section

namespace Authentication

/--
A request that changes nothing. A wrong code is not one of these: it advances the attempt's
failure count, and that count has to be persisted for the entry budget of AUTH-5.2.7 to mean
anything, so it is an ordinary transition with a rejection among its effects.
-/
inductive AuthError where
  | attemptNotLive
  | attemptExpired
  | unknownToken
  | notOriginatingBrowser
  | codeNotYetAvailable
  | emailedCodeNotEnabled
  | invitationNotPending
  | invitationExpired
  /-- This tenant does not admit the means by which this route proves an address, so no attempt
  is minted and no mail is sent (AUTH-9.9.4). The invitation is untouched, and the person's way
  in is whichever kind the tenant does admit. -/
  | originNotPermitted
  /-- Refused by the rate limiter (AUTH-14.1.1). Distinct from the others because nothing about
  the request was wrong; it is the rate that was. -/
  | throttled
  deriving DecidableEq, Repr, Inhabited

end Authentication
