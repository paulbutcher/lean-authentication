/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Authentication

/-!
The development transport.

A developer using it has nothing but the sink to sign in from, so what is worth checking is that
the message arrives whole: a rendering that dropped or truncated the text body would leave them
with no link and no code.
-/

namespace Tests.Transport
open Authentication

private def address (raw : String) : EmailAddress :=
  (EmailAddress.parse raw).toOption.getD default

private def body : String :=
  "Open this link to sign in:\n\n"
    ++ "https://auth.example.com/t/acme/signin/link?attempt=a1&token=t1\n\n"
    ++ "Or type this code: 1234-5678\n"

private def sample (key : String) : OutboundEmail :=
  { «from» := { address := address "sign-in@auth.example.com", displayName := "Acme" }
    to := address "person@example.com"
    subject := "Sign in to Acme"
    textBody := body
    idempotencyKey := key }

/-- Whatever the message and whatever the sink, the id is the message's own idempotency key, so
a caller keying off it sees what a real transport would have returned. -/
theorem capturing_reports_idempotencyKey (sink : OutboundEmail → Id Unit) (mail : OutboundEmail) :
    (EmailTransport.capturing sink).send mail = .ok ⟨mail.idempotencyKey⟩ := rfl

/-- Substring containment, which is the shape of every claim below. A theorem would be the
stronger form, but `String` carries no infix lemmas to close one with. -/
private def occurs (needle haystack : String) : Bool := (haystack.splitOn needle).length > 1

def checks : IO (List (String × Bool)) := do
  let sent ← IO.mkRef ([] : List OutboundEmail)
  let transport := EmailTransport.capturing (m := IO) fun mail => sent.modify (· ++ [mail])
  let first ← transport.send (sample "key-1")
  let _ ← transport.send (sample "key-2")
  let captured ← sent.get
  let rendered := (sample "key-1").render
  pure
    [ ("transport: every message reaches the sink, in the order it was sent",
        captured.map (·.idempotencyKey) == ["key-1", "key-2"]),
      ("transport: the reported id is the message's idempotency key",
        (first.toOption.map (·.value)) == some "key-1"),
      ("transport: the rendering names the recipient and the subject",
        occurs "person@example.com" rendered && occurs "Sign in to Acme" rendered),
      ("transport: the rendering carries the whole text body", occurs body rendered) ]

end Tests.Transport
