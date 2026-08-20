/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Authentication.Tenant
public import Authentication.Time

/-!
Consent records (§4.6).

What a person agreed to, which version of it they were shown, and when.

The library stores these and does not capture them. There is no consent field on any form it
serves, because whether a sign-in is about to create an account is exactly the fact §14.2 exists
to hide, and a control that appeared only for addresses with no account would answer that before
any mail was sent, to anyone who cared to look at the page. The client asks somebody who is
already signed in, at whatever moment suits it, and records what they said here (AUTH-4.6.1).

Nothing here is interpreted. The subject and the version are the client's own words, the way an
invitation's metadata is (AUTH-8.7): this records that something was agreed to, not what.

The history is append only, for the same reason the audit log is. What it holds is evidence, and
evidence the holder can rewrite afterwards is not evidence, so a withdrawal is another entry
rather than an edit to the entry that granted.
-/

public section

namespace Authentication

inductive ConsentAct where
  | granted
  | withdrawn
  deriving DecidableEq, Repr, Inhabited

/-- What was agreed to, named by the client. A separate type from the version because both are
strings and an argument list that took two would let them be swapped silently. -/
structure ConsentSubject where
  name : String
  deriving DecidableEq, Repr, Inhabited

/-- One thing a person said about one subject, at one moment. -/
structure ConsentEntry (tenant : TenantId) where
  account : AccountId tenant
  subject : ConsentSubject
  /-- Which version was in front of them. On a withdrawal it is the version being withdrawn
  from, which the client knows because it has just shown it to them. -/
  version : String
  act : ConsentAct
  recordedAt : Timestamp
  deriving DecidableEq, Repr

/-- Where one subject stands now, which is the last thing the person said about it. -/
structure ConsentState where
  subject : ConsentSubject
  version : String
  granted : Bool
  since : Timestamp
  deriving DecidableEq, Repr, Inhabited

namespace Consent

/-- A history is oldest first, so the last entry about a subject is the current answer. -/
def latest {tenant : TenantId} (history : List (ConsentEntry tenant))
    (subject : ConsentSubject) : Option (ConsentEntry tenant) :=
  (history.filter (·.subject == subject)).getLast?

/-- Silence is not consent: a subject nobody has been asked about is not granted. -/
def granted {tenant : TenantId} (history : List (ConsentEntry tenant))
    (subject : ConsentSubject) : Bool :=
  match latest history subject with
  | some entry => entry.act == .granted
  | none => false

def subjects {tenant : TenantId} (history : List (ConsentEntry tenant)) : List ConsentSubject :=
  (history.map (·.subject)).eraseDups

/-- Every subject this account has been asked about, in the order it was first asked. -/
def state {tenant : TenantId} (history : List (ConsentEntry tenant)) : List ConsentState :=
  (subjects history).filterMap fun subject =>
    (latest history subject).map fun entry =>
      { subject
        version := entry.version
        granted := entry.act == .granted
        since := entry.recordedAt }

end Consent

end Authentication
