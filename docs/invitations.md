# Inviting people

An invitation lets one address into one tenant. It is how people join an [invite-only tenant](signup.md#invited-people-only), and how named outsiders join a tenant restricted to its own domains. It is also where your own roles travel, since the library has none.

## Sending one

```lean
def inviteEditor {tenant : TenantId} (ports : Service.Ports IO) (config : TenantConfig tenant)
    (address : EmailAddress) (inviter : String) :
    IO (Except Service.InvitationRefusal (Service.InvitationIssued tenant)) :=
  Service.createInvitation ports config address ⟨"editor"⟩ (createdBy := .client inviter)
```

The library mails the link and checks no permissions: deciding who may invite is your application's job, and the library ships no route that does it. `createdBy` goes into the audit log exactly as you give it, so it records who your application said acted, not who was entitled to.

Accepting runs the ordinary sign-in flow, cross-device code included, and the account it creates is always for the invited address in the invited tenant, whatever the request says. An address that already has an account is signed in, and the invitation is spent.

## Managing them

```lean
let _ ← Service.invitations (tenant := tenant) ports
let _ ← Service.resendInvitation ports config id
let _ ← Service.revokeInvitation ports id
```

`invitations` lists each with its standing: pending, accepted, expired or revoked. An invitation lasts `TenantConfig.invitationLifetime`, 7 days by default, and is single use. Resending issues a new link and the old one stops working.

## Tenants without the magic link

An invitation lets in an address, whatever it signs in with. Where the tenant's `originPolicy` does not admit the magic link, the mail links to the first provider in `TenantConfig.providers` instead, and the provider has to assert the invited address. Where nothing the tenant admits could create an account, a passkey-only tenant for instance, `createInvitation` refuses with `noWayToAccept` rather than mail a link nobody could follow.

## Roles

The metadata, `⟨"editor"⟩` above, is your own text: stored verbatim, never read, and handed back when the invitation is accepted. Put whatever your application needs to set the new account up there.

Every route that can create an account tells you when it has, through `onAdmitted` on `Http.Config` and `OidcHttp.Config`. You are told whether the account is the first in its tenant, which is the signal for making somebody its owner, and given the metadata of the invitation it accepted:

```lean
def assignRole {tenant : TenantId} (admitted : Service.AccountAdmitted tenant) : IO Unit :=
  match admitted.invitationMetadata with
  | some role => IO.println s!"{admitted.account.value} joins as {role.payload}"
  | none =>
    if admitted.firstInTenant then IO.println s!"{admitted.account.value} owns the tenant"
    else pure ()
```

```lean
def http (ports : Service.Ports IO) (tenant : (t : TenantId) → IO (Option (TenantConfig t))) :
    Http.Config :=
  { ports, tenant, onAdmitted := fun _ admitted => assignRole admitted }
```

It runs before the response is sent, so whatever it sets up is there when the browser arrives. A client driving `Service` itself reads the same record from `Outcome.admitted`.
