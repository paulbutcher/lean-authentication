/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Authentication.Pepper
public import Authentication.Store
public import AuthenticationOAuth.Port.ClientMetadata
public import AuthenticationOAuth.Store

/-!
The implementations an authorisation server is wired from (§20.2).
-/

public section

namespace Authentication.OAuth.Service

open Authentication

/-- The implementations chosen at startup, together with the peppers in force. `store` is the
core port, reached for the browser's session and for consent; a grant is a consent record and
was never going to live anywhere else.

`documents` is absent unless the deployment has somewhere to fetch a client's metadata document
from, which depends on what network this server is on rather than on the protocol. It is the one
field here the metadata document reports, so that what is advertised and what can be resolved
cannot disagree. -/
structure Ports (m : Type → Type) where
  store : AuthStore m
  oauth : OAuthStore m
  documents : Option (ClientDocuments m) := none
  peppers : PepperRing

end Authentication.OAuth.Service
