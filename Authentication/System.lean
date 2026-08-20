/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Authentication.Port.Clock
public import Std.Time

/-!
The ordinary implementations of `Clock` and `RandomBytes`: the host's wall clock and the
operating system's cryptographically secure source.

They are definitions here and instances in `Authentication.Instances`, so that a client can
either import that module or write

```lean
instance : Clock IO := Clock.system
```

where its own code can see it.
-/

public section

namespace Authentication

/-- Epoch seconds from the host's wall clock. A deployment whose nodes disagree about the time,
or which wants the database's clock to be the authority, supplies its own. -/
@[instance_reducible]
def Clock.system : Clock IO where
  now := do pure ⟨(← Std.Time.Timestamp.now).toSecondsSinceUnixEpoch.val⟩

/-- `getrandom(2)`, which satisfies AUTH-5.3.1. A deployment drawing from an HSM or a validated
module supplies its own. -/
@[instance_reducible]
def RandomBytes.system : RandomBytes IO where
  draw count := do pure (.ok (← IO.getRandomBytes count.toUSize))

end Authentication
