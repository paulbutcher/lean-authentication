/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import AuthenticationSqlite

/-!
The federated route into a session, driven through a real store (AUTH-6.7, AUTH-6.10).

`Federation.decide` is proved over in `Tests.Federation`; what cannot be proved there is that the
decision is reached from the rows the store actually holds, and that the account it names is the
one the session is issued for. That is what these drive.
-/

namespace Tests.FederatedSignIn
open Authentication Authentication.Service

initialize clockRef : IO.Ref Timestamp ← IO.mkRef ⟨1700000000⟩
initialize drawCounter : IO.Ref Nat ← IO.mkRef 0

instance : Clock IO where
  now := clockRef.get

instance : RandomBytes IO where
  draw count := do
    let index ← drawCounter.modifyGet fun n => (n, n + 1)
    pure (.ok ((Leancrypto.Sha256.hashUtf8 s!"federated-seed-{index}").extract 0 count))

private def address (raw : String) : EmailAddress := (EmailAddress.parse raw).toOption.getD default

private def peppers : PepperRing :=
  { current := { keyId := ⟨"pepper-1"⟩, secret := Leancrypto.Sha256.hashUtf8 "federated pepper" } }

private def portsOn (db : SQLite) : Ports IO :=
  { store := Sqlite.store db
    transport := EmailTransport.capturing (fun _ => pure ())
    responsePolicy := SignInResponsePolicy.silent IO
    limiter := RateLimiter.unlimited IO
    responseFloor := ResponseFloor.immediate IO
    humanCheck := HumanCheck.unchecked IO
    peppers }

private def configFor (tenant : TenantId) (policy : SignupPolicy := .unrestricted) :
    TenantConfig tenant :=
  { displayName := "Acme"
    baseUrl := ⟨"https://auth.example.com"⟩
    sendingIdentity :=
      { address := address "sign-in@auth.example.com", displayName := "Acme sign-in" }
    signupPolicy := policy }

private def google : FederatedIdentity := ⟨"https://accounts.google.test", "google-subject-1"⟩

private def subjectFor (tenant : TenantId) (raw : String) (identity : FederatedIdentity)
    (verified : Bool) : SessionSubject tenant :=
  { origin := .federated identity verified
    address := address raw
    requester := { ip := none, userAgent := none, approximateLocation := none } }

private def openDb : IO SQLite := do
  let db ← SQLite.openWith ":memory:" .readWriteCreate
  db.exec Sqlite.createSchemaSql
  pure db

def checks : IO (List (String × Bool)) := do
  let tenant : TenantId := ⟨"acme"⟩
  let config := configFor tenant

  -- A stranger the provider vouches for gets an account and a session.
  let db ← openDb
  let ports := portsOn db
  let first ← issueFor ports config (subjectFor tenant "person@example.com" google true)
  let createdAccount := first.admitted.map (·.account)

  -- The same provider identity again signs the same account in, and makes no second account.
  let again ← issueFor ports config (subjectFor tenant "person@example.com" google true)
  let credentials ← match createdAccount with
    | some account => ports.store.credentialsForAccount tenant account
    | none => pure []

  -- The address changed at the provider; the subject did not. AUTH-6.6 says the subject wins.
  let renamed ← issueFor ports config (subjectFor tenant "moved@example.com" google true)
  let renamedSession := renamed.session.isSome
  let accountsAfterRename ← ports.store.accountByIdentity tenant (address "moved@example.com").normalise

  -- A different provider identity asserting an address this tenant already holds, unverified.
  let other : FederatedIdentity := ⟨"https://accounts.google.test", "google-subject-2"⟩
  let unverified ← issueFor ports config (subjectFor tenant "person@example.com" other false)

  -- The same identity, now verified, links to the account that already proved the address.
  let linked ← issueFor ports config (subjectFor tenant "person@example.com" other true)
  let linkedCredentials ← match createdAccount with
    | some account => ports.store.credentialsForAccount tenant account
    | none => pure []

  -- The signup policy applies to this route exactly as it does to the other (AUTH-6.10).
  let closed ← openDb
  let closedPorts := portsOn closed
  let inviteOnly := configFor tenant .inviteOnly
  let refusedSignup ← issueFor closedPorts inviteOnly
    (subjectFor tenant "outsider@example.com" google true)
  let noAccount ← closedPorts.store.accountByIdentity tenant (address "outsider@example.com").normalise

  -- A deactivated account is not signed in by a provider either (AUTH-9.6).
  let dormant ← openDb
  let dormantPorts := portsOn dormant
  let made ← issueFor dormantPorts config (subjectFor tenant "sleepy@example.com" google true)
  let _ ← match made.admitted.map (·.account) with
    | some account => dormantPorts.store.setAccountStatus tenant account .deactivated
    | none => pure (.ok ())
  let afterDeactivation ← issueFor dormantPorts config
    (subjectFor tenant "sleepy@example.com" google true)

  pure
    [ ("federated: a verified stranger is admitted and gets a session",
        first.session.isSome && createdAccount.isSome)
    , ("federated: the same identity signs the same account in",
        again.session.isSome && again.admitted.isNone)
    , ("federated: and is linked once, not once per sign-in", credentials.length == 1)
    , ("federated: an address the provider changed still signs in the same account (AUTH-6.6)",
        renamedSession && accountsAfterRename.isNone)
    , ("federated: an unverified assertion links to nothing (AUTH-6.7)",
        unverified.session.isNone && unverified.refused == some .addressNotVerified)
    , ("federated: the same identity verified links to the account holding the address",
        linked.session.isSome && linked.admitted.isNone)
    , ("federated: linking adds a credential rather than an account",
        linkedCredentials.length == 2)
    , ("federated: an invitation-only tenant refuses a federated stranger (AUTH-6.10)",
        refusedSignup.session.isNone && noAccount.isNone)
    , ("federated: a deactivated account is not signed in by a provider",
        afterDeactivation.session.isNone
          && afterDeactivation.refused == some .accountDeactivated) ]


/--
Unlinking, and the refusal that makes it more than a delete (AUTH-6.8).

The refusal is reachable only because the magic link stops being a way in when the address is
suppressed, which is what these establish: the same unlink is allowed before the address bounces
and refused after.
-/
def unlinkChecks : IO (List (String × Bool)) := do
  let tenant : TenantId := ⟨"acme"⟩
  let config := configFor tenant
  let db ← openDb
  let ports := portsOn db
  let made ← issueFor ports config (subjectFor tenant "person@example.com" google true)
  let account := (made.admitted.map (·.account)).getD ⟨""⟩
  let second : FederatedIdentity := ⟨"https://other.test", "other-subject"⟩
  let _ ← issueFor ports config (subjectFor tenant "person@example.com" second true)
  let held ← linkedIdentities ports account
  let strangers ← openDb
  let strangerPorts := portsOn strangers
  let _ ← issueFor strangerPorts config (subjectFor tenant "elsewhere@example.com" google true)

  -- Two credentials and a mailable address: removing one leaves two ways in.
  let first ← unlinkIdentity ports account ((held[0]?.map (·.id)).getD ⟨""⟩)
  let afterFirst ← linkedIdentities ports account

  -- One credential left, and the address still works, so it still goes.
  let ok := match first with | .ok _ => true | .error _ => false

  -- Now suppress the address and try to remove the last one.
  let identity := (address "person@example.com").normalise
  let _ ← ports.store.suppressAddress tenant identity ⟨1700000000⟩ "bounced"
  let last ← unlinkIdentity ports account ((afterFirst[0]?.map (·.id)).getD ⟨""⟩)
  let afterLast ← linkedIdentities ports account

  -- A credential identifier that is not this account's is refused rather than acted on.
  let foreign ← unlinkIdentity ports account ⟨"not-a-credential"⟩
  let unlinkEntries ← ports.store.auditEntries tenant

  pure
    [ ("unlink: a credential goes while another way in remains", ok && afterFirst.length == 1)
    , ("unlink: the last one is refused once the address is suppressed (AUTH-6.8)",
        match last with | .error .lastWayIn => true | _ => false)
    , ("unlink: and the credential is still there", afterLast.length == 1)
    , ("unlink: an identifier this account does not hold is refused",
        match foreign with | .error .notThisAccount => true | _ => false)
    , ("unlink: it is recorded, naming the provider (AUTH-14.1.7)",
        unlinkEntries.any
          (·.event == .identityUnlinked account "https://accounts.google.test")) ]

/--
Linking authorised by holding the account rather than by an address (AUTH-6.7.1).

The address is what these have to show is not consulted. An identity asserting nothing at all
links, because holding the account is the whole of the evidence, and that is the case Apple's
private relay makes unavoidable: there is no address for an account to match.
-/
def linkChecks : IO (List (String × Bool)) := do
  let tenant : TenantId := ⟨"acme"⟩
  let config := configFor tenant
  let db ← openDb
  let ports := portsOn db
  let made ← issueFor ports config (subjectFor tenant "person@example.com" google true)
  let account := (made.admitted.map (·.account)).getD ⟨""⟩
  let stranger : FederatedIdentity := ⟨"https://accounts.google.test", "google-subject-2"⟩
  let other ← issueFor ports config (subjectFor tenant "stranger@example.com" stranger true)
  let otherAccount := (other.admitted.map (·.account)).getD ⟨""⟩

  -- An identity nobody holds, asserting an address no account has verified.
  let fresh : FederatedIdentity := ⟨"https://appleid.test", "001234.relay"⟩
  let linked ← linkIdentity ports account fresh
  let held ← linkedIdentities ports account
  let again ← linkIdentity ports account fresh
  let afterAgain ← linkedIdentities ports account

  -- The same identity cannot be moved to a second account, which is the takeover by another name.
  let stolen ← linkIdentity ports otherAccount fresh

  let unknown ← linkIdentity ports (⟨"no-such-account"⟩ : AccountId tenant) fresh
  let _ ← deactivateAccount ports otherAccount
  let dead ← linkIdentity ports otherAccount ⟨"https://appleid.test", "other.relay"⟩
  let entries ← ports.store.auditEntries tenant

  pure
    [ ("link: a session-authorised link needs no address agreement (AUTH-6.7.1)",
        (match linked with | .ok _ => true | .error _ => false)
          && held.length == 2)
    , ("link: linking the same identity again changes nothing and does not fail",
        (match again with | .ok _ => true | .error _ => false)
          && afterAgain.length == held.length)
    , ("link: an identity another account holds is refused, not moved",
        match stolen with | .error .alreadyLinked => true | _ => false)
    , ("link: an account this tenant does not have is refused",
        match unknown with | .error .unknownAccount => true | _ => false)
    , ("link: a deactivated account gains no way in",
        match dead with | .error .accountDeactivated => true | _ => false)
    , ("link: it is recorded, naming the provider (AUTH-14.1.7)",
        entries.any (·.event == .identityLinked account "https://appleid.test")) ]

end Tests.FederatedSignIn
