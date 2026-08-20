/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Authentication.Email
public import Authentication.Tenant
public import Authentication.Time

/-!
Bounces and suppression (§12).

Continuing to write to an address that has hard bounced is how a sending domain's reputation is
spent, and the person on the other end never sees any of it: the mail that stops arriving is
everyone else's.

What a provider reports is normalised into `DeliveryEvent` here, so the two transports agree on
what a bounce is and the store holds one shape. The provider's own timestamp is not among the
fields, deliberately: it arrives as text in a format that differs by provider, and the only
question anything here asks of it is how recent the failure was, which the clock at ingestion
answers without a date parser.
-/

public section

namespace Authentication

/-- Why an address was refused, of the reasons that are permanent. A mailbox that was full on
Tuesday is not an address nobody may write to again, which is why transient failures are counted
(AUTH-12.5) and not suppressed. -/
inductive SuppressionReason where
  | hardBounce
  | spamComplaint
  /-- Suppressed by the client rather than by a provider. Clients acquire addresses from places
  this library never sees, and one of them saying "never write here" needs somewhere to go. -/
  | client
  deriving DecidableEq, Repr, Inhabited

inductive DeliveryFailure where
  | hardBounce
  | spamComplaint
  | softBounce
  deriving DecidableEq, Repr, Inhabited

/-- Which failures suppress. Returning the reason rather than a `Bool` is what keeps a record
from claiming it was suppressed by a soft bounce. -/
def DeliveryFailure.suppression : DeliveryFailure → Option SuppressionReason
  | .hardBounce => some .hardBounce
  | .spamComplaint => some .spamComplaint
  | .softBounce => none

/-- One thing a provider said about one message. -/
structure DeliveryEvent where
  address : EmailAddress
  failure : DeliveryFailure
  /-- The provider's own words, for whoever has to work out why. Never shown to the person, who
  did not ask for the mail and cannot act on `550 5.1.1`. -/
  detail : String := ""
  /-- The idempotency key the message carried, which names the attempt it belonged to
  (AUTH-10.4). -/
  reference : Option String := none
  deriving DecidableEq, Repr, Inhabited

/-- One address's history in one tenant. Keyed per tenant so that one tenant's bounce history is
not observable through another tenant's behaviour (AUTH-12.2). -/
structure DeliveryRecord (tenant : TenantId) where
  address : NormalisedEmail
  /-- `none` while every failure has been transient: observed and counted, not refused. -/
  suppressedBy : Option SuppressionReason := none
  failures : Nat
  firstFailureAt : Timestamp
  lastFailureAt : Timestamp
  detail : String := ""
  deriving DecidableEq, Repr

namespace DeliveryRecord

def suppressed {tenant : TenantId} (record : DeliveryRecord tenant) : Bool :=
  record.suppressedBy.isSome

/-- What one more failure makes of a record. A suppression already in force is not lifted by a
later transient failure; only the client lifts it (AUTH-12.4). -/
def afterFailure {tenant : TenantId} (record : DeliveryRecord tenant) (failure : DeliveryFailure)
    (now : Timestamp) (detail : String) : DeliveryRecord tenant :=
  { record with
    suppressedBy := failure.suppression.orElse fun _ => record.suppressedBy
    failures := record.failures + 1
    lastFailureAt := now
    detail }

def first {tenant : TenantId} (address : NormalisedEmail) (failure : DeliveryFailure)
    (now : Timestamp) (detail : String) : DeliveryRecord tenant :=
  { address
    suppressedBy := failure.suppression
    failures := 1
    firstFailureAt := now
    lastFailureAt := now
    detail }

end DeliveryRecord

end Authentication
