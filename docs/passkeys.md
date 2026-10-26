# Passkeys

A passkey is the only phishing-resistant way in this library offers: the browser binds the signature to your origin, so there is no code anybody can be talked into typing somewhere else. Two targets, because verifying a signature links OpenSSL and the magic link routes must not: `AuthenticationPasskey` speaks WebAuthn and `AuthenticationPasskeyHttp` serves it.

A passkey signs in an account that already exists; it never creates one. People join the way they always did, by magic link, provider or invitation, and add a passkey once signed in. An account whose magic link still works is only as strong as its mailbox, so [the origin policy](enforce-sso.md) is what makes a passkey the floor rather than the ceiling.

## The relying party

```lean
passkeyRelyingParty := some
  { id := "example.com"                      -- or "app.example.com", and not changeable after
    origins := ["https://app.example.com"] }
```

The relying party is configured, never derived from the base URL. WebAuthn accepts the origin's host or any registrable suffix of it, and the choice decides whether one passkey works across your subdomains. **Every passkey registered is bound to the identifier chosen, for good.** A tenant that configures none offers no passkeys.

## Mounting

```lean
def app (ports : Service.Ports IO) : Routing.StatelessHandler .std :=
  let tenant := fun t => pure (some (config t))
  Routing.toHandler
    (Http.routes { ports, tenant } ++
      PasskeyHttp.routes { ports, verifier := Passkey.verifier, tenant })
```

| Path | Method |
| --- | --- |
| `/t/<tenant>/passkey/register` | `POST`, begins a registration for the session's account |
| `/t/<tenant>/passkey/register/complete` | `POST`, the authenticator's answer |
| `/t/<tenant>/passkey/signin` | `POST`, begins a sign-in |
| `/t/<tenant>/passkey/signin/complete` | `POST`, the assertion |
| `/t/<tenant>/passkey/recover` | `POST`, begins a registration under a [recovery grant](recovery.md) |
| `/t/<tenant>/passkey/recover/complete` | `POST`, the authenticator's answer, with no session |

The registration routes take the account from the session cookie and nowhere else, which is their whole forgery defence. The sign-in routes take no session, so do not mount them behind a guard that wants one.

## The script is yours

`navigator.credentials` can only be called from script, so these routes answer JSON and serve no page. The script belongs to your page, and is about this much. Every binary value travels as base64url, in both directions. It was run once, by hand, against these routes with Chromium's virtual authenticator; the suite does not run it:

```js
const decode = s => Uint8Array.from(atob(s.replace(/-/g, "+").replace(/_/g, "/")), c => c.charCodeAt(0));
const encode = b => btoa(String.fromCharCode(...new Uint8Array(b)))
  .replace(/\+/g, "-").replace(/\//g, "_").replace(/=+$/, "");
const post = (url, body) => fetch(url, { method: "POST", headers: { "content-type": "application/json" },
  body: body && JSON.stringify(body) }).then(r => r.json());

async function addPasskey(tenant, label) {
  const options = await post(`/t/${tenant}/passkey/register`);
  const created = await navigator.credentials.create({ publicKey: { ...options,
    challenge: decode(options.challenge),
    user: { ...options.user, id: decode(options.user.id) },
    excludeCredentials: options.excludeCredentials.map(c => ({ ...c, id: decode(c.id) })) } });
  return post(`/t/${tenant}/passkey/register/complete`, { label,
    attestationObject: encode(created.response.attestationObject),
    clientDataJSON: encode(created.response.clientDataJSON),
    transports: created.response.getTransports?.() ?? [] });
}

async function signInWithPasskey(tenant, returnTo) {
  const query = returnTo ? `?returnTo=${encodeURIComponent(returnTo)}` : "";
  const options = await post(`/t/${tenant}/passkey/signin${query}`);
  const asserted = await navigator.credentials.get({ publicKey: { ...options,
    challenge: decode(options.challenge) } });
  const answer = await post(`/t/${tenant}/passkey/signin/complete`, { id: asserted.id,
    authenticatorData: encode(asserted.response.authenticatorData),
    clientDataJSON: encode(asserted.response.clientDataJSON),
    signature: encode(asserted.response.signature),
    userHandle: asserted.response.userHandle && encode(asserted.response.userHandle) });
  if (answer.signedIn) location.assign(answer.returnTo);
  return answer.signedIn;
}
```

Pass `signInWithPasskey` the `returnTo` your sign-in page was given, which is how the [authorisation server](authorisation-server.md) gets its request back after a sign-in. The completion answers where to land, already checked against `returnToAllowlist` and falling back to `defaultReturnTo`; redirect there, never to the value the page was handed.

Every refusal answers the same body, `{"error": "rejected"}`; `PasskeyHttp.Config.observeRefusal` is where the reason reaches you.

## Managing an account's passkeys

```lean
let _ ← Service.passkeys ports account
let _ ← Service.renamePasskey ports account id "Work laptop"
let _ ← Service.unlinkIdentity ports config account id
```

Removal refuses to take away an account's last way in. On a tenant that admits the magic link, the primary address counts as one.

## What is and is not checked

- ES256 only; any other algorithm is refused by its identifier rather than attempted.
- Discoverable credentials only, so signing in takes no address and there is nothing to enumerate.
- No attestation is verified: `none` is accepted, and every other format is recorded but not acted on.
- A signature counter that fails to advance is audited, not refused, because a passkey synced between devices reports zero from each.

## Passkeys only

`originPolicy := .only [.passkey]` is allowed, and existing accounts with passkeys keep signing in. But nothing can then create an account: a passkey cannot, and an invitation is refused with `noWayToAccept`. A tenant like that takes no new members, so admit a provider beside passkeys if it needs to grow. Somebody who loses their only passkey is [recovered by grant](recovery.md).
