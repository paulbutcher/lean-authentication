/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Authentication.Suppression
import Authentication.Tenant

/-!
Provider callbacks (AUTH-12.1.1).

An endpoint that accepts a delivery event has to establish that the provider sent it, and how is
entirely the provider's business: Postmark presents credentials, SNS signs with a certificate the
receiver fetches. Both answers need the request as it arrived, which the transports cannot see and
the routes cannot interpret, so this is the seam between them.

Verification happens inside `accept`, before anything is returned. There is deliberately no way to
obtain the events without it: a route holding a `WebhookEndpoint` cannot forget to check, because
checking is not a separate call it could omit.
-/

public section

namespace Authentication

inductive WebhookOutcome where
  | ingest (events : List DeliveryEvent)
  /-- Verified, and there is nothing to record: a delivery notice, an open, or a handshake the
  endpoint answered itself. Distinct from `rejected` because the provider must be told the
  difference, and distinct from an empty `ingest` because that would read as a payload nobody
  understood. -/
  | accepted
  | rejected
  deriving Repr, Inhabited

structure WebhookEndpoint (m : Type → Type) where
  /-- The last segment of the path this endpoint answers on, so that two providers configured at
  once do not need two route tables. -/
  name : String
  /-- The tenant from the path, a lookup over the request's headers, and the body as it arrived.
  Headers arrive as a function rather than a list so that nothing here needs an HTTP library. -/
  accept : TenantId → (String → Option String) → String → m WebhookOutcome

end Authentication
