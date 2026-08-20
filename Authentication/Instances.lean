/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Authentication.System

/-!
`Clock` and `RandomBytes` for `IO`, as instances.

Importing this module is what turns them on. Nothing else in the package imports it, so a module
that means to pin the clock and forgets still fails to resolve the instance rather than quietly
running against the real one.

They are declared at low priority, so a client's own instance wins wherever it is in scope
without needing to say anything.
-/

public section

namespace Authentication

instance (priority := low) : Clock IO := Clock.system
instance (priority := low) : RandomBytes IO := RandomBytes.system

end Authentication
