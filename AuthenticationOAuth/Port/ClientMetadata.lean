/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Authentication.Time
public import Json

/-!
The one port this target adds (§20.2).

Resolving a client identifier that is a URL means fetching that URL, and the protocol core
performs no I/O. This is the whole of the seam: an adapter is a `GET`, and nothing above it
knows what performed the request.

The result carries more than the document because two of the requirements are about the
response rather than its body. Caching is to respect the response's cache headers, which do not
survive being parsed into JSON, and the recommended size limit is on the bytes received. Both
therefore arrive here as data, and are enforced where the document is validated.
-/

public section

namespace Authentication.OAuth

structure FetchedDocument where
  document : Json
  /-- How long the response's cache headers permit it to be held. `none` means the response said
  nothing, which is not the same as saying zero: the client ID metadata document draft §5 lets
  the server apply its own bound in that case. -/
  freshFor : Option Duration := none
  /-- The size of the body as received. The draft §6.6 recommends a five kilobyte maximum, and
  it is checked where the document is validated rather than trusted to whoever fetched it. -/
  size : Nat

/--
Fetching a client's metadata document.

An adapter refuses anything but `https`, follows no redirect to a host it would not have
fetched in the first place, and applies a timeout: the request is made on a caller's say-so, and
what it costs is this server's own network position (draft §6.5). The identifier is checked
against private and loopback addresses before it reaches here, which is a floor rather than a
substitute.
-/
structure ClientDocuments (m : Type → Type) where
  fetch : String → m (Except String FetchedDocument)

end Authentication.OAuth
