// Captures a whole passkey ceremony from Chrome's virtual authenticator: a registration and an
// assertion made by the same credential, over challenges this script chose.
//
// Run as `node make-passkey-capture.mjs <dir>` from a directory where Playwright is installed:
//
//   npm install playwright && npx playwright install --with-deps chromium
//
// Playwright is resolved from the working directory rather than from beside this file, so the
// script stays committed here and the toolchain stays out of the repository. Nothing in the
// suite runs it: the output is committed and read as a fixture, because AUTH-16.5 forbids a
// committed test from reaching anything.
//
// The point is the one `make-passkey-fixtures.sh` makes and cannot finish. That script lays its
// bytes out from the specification, so a misreading would be consistent across the fixture and
// the parser; these bytes come from Chrome's own CTAP2 implementation and its own key, and the
// public key the assertion verifies against is the one read out of the registration. Nothing in
// the loop was produced by this repository.
//
// The relying party is `localhost` because WebAuthn treats it as a secure origin without a
// certificate, and the port is fixed so the recorded origin does not change between runs.

import { createServer } from 'node:http'
import { writeFileSync } from 'node:fs'
import { createRequire } from 'node:module'
import { pathToFileURL } from 'node:url'

const require = createRequire(pathToFileURL(process.cwd() + '/'))
const { chromium } = require('playwright')

const out = process.argv[2]
if (!out) {
  console.error('usage: node make-passkey-capture.mjs <dir>')
  process.exit(1)
}

const port = 8766
const relyingPartyId = 'localhost'
const origin = `http://${relyingPartyId}:${port}`
const registrationChallenge = 'cmVnaXN0cmF0aW9uLWNoYWxsZW5nZS0wMQ'
const assertionChallenge = 'YXNzZXJ0aW9uLWNoYWxsZW5nZS0wMQ'
const userHandle = 'YWNjb3VudC0x'

const server = createServer((_, response) => {
  response.writeHead(200, { 'content-type': 'text/html; charset=utf-8' })
  response.end('<!doctype html><meta charset="utf-8"><title>capture</title>')
})
await new Promise(resolve => server.listen(port, '127.0.0.1', resolve))

const browser = await chromium.launch()
const page = await browser.newPage()
const session = await page.context().newCDPSession(page)
await session.send('WebAuthn.enable')
// A platform authenticator with resident keys, which is the only kind this library registers,
// and presence and verification simulated so nothing waits for a gesture nobody can make.
const { authenticatorId } = await session.send('WebAuthn.addVirtualAuthenticator', {
  options: {
    protocol: 'ctap2',
    ctap2Version: 'ctap2_1',
    transport: 'internal',
    hasResidentKey: true,
    hasUserVerification: true,
    isUserVerified: true,
    automaticPresenceSimulation: true,
  },
})

await page.goto(origin)

const captured = await page.evaluate(async args => {
  const decode = text => {
    const padded = text.replace(/-/g, '+').replace(/_/g, '/')
    const raw = atob(padded + '='.repeat((4 - (padded.length % 4)) % 4))
    return Uint8Array.from(raw, c => c.charCodeAt(0))
  }
  const encode = buffer =>
    btoa(String.fromCharCode(...new Uint8Array(buffer)))
      .replace(/\+/g, '-')
      .replace(/\//g, '_')
      .replace(/=+$/, '')

  const created = await navigator.credentials.create({
    publicKey: {
      challenge: decode(args.registrationChallenge),
      rp: { id: args.relyingPartyId, name: 'Capture' },
      user: {
        id: decode(args.userHandle),
        name: 'person@example.com',
        displayName: 'person@example.com',
      },
      pubKeyCredParams: [{ type: 'public-key', alg: -7 }],
      authenticatorSelection: { residentKey: 'required', userVerification: 'preferred' },
      attestation: 'none',
    },
  })

  // No `allowCredentials`: a discoverable credential is what the authenticator offers, which is
  // the whole reason this library registers no other kind.
  const asserted = await navigator.credentials.get({
    publicKey: {
      challenge: decode(args.assertionChallenge),
      rpId: args.relyingPartyId,
      userVerification: 'preferred',
    },
  })

  return {
    registration: {
      id: created.id,
      attestationObject: encode(created.response.attestationObject),
      clientDataJSON: encode(created.response.clientDataJSON),
      transports: created.response.getTransports ? created.response.getTransports() : [],
    },
    assertion: {
      id: asserted.id,
      authenticatorData: encode(asserted.response.authenticatorData),
      clientDataJSON: encode(asserted.response.clientDataJSON),
      signature: encode(asserted.response.signature),
      userHandle: asserted.response.userHandle ? encode(asserted.response.userHandle) : null,
    },
  }
}, { registrationChallenge, assertionChallenge, relyingPartyId, userHandle })

await session.send('WebAuthn.removeVirtualAuthenticator', { authenticatorId })
await browser.close()
server.close()

writeFileSync(
  `${out}/passkey-capture.json`,
  JSON.stringify(
    {
      source: 'Chrome DevTools Protocol virtual authenticator, via Playwright',
      relyingPartyId,
      origin,
      registrationChallenge,
      assertionChallenge,
      userHandle,
      ...captured,
    },
    null,
    2,
  ) + '\n',
)

console.log(`wrote ${out}/passkey-capture.json`)
