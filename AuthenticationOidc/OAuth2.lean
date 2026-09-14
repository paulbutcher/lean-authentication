/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import AuthenticationOidc.SignIn

/-!
A provider that is not OpenID Connect (AUTH-6.9).

GitHub is the one this was written against. It answers the token request with an access token and
nothing else, so who somebody is takes a second call, and whether their address is verified takes a
third. None of that is made to look like an ID token: it produces the same `ProviderAnswer` through
a different implementation of the same port, which is what AUTH-6.9 asks for.

What is lost by not being OpenID Connect is worth naming. There is no signature over the claims, so
the answers are trusted because they arrived over TLS from an endpoint the configuration named,
authenticated by a token this server just obtained. The `nonce` of AUTH-6.3 has nothing to bind to
either; what stands in for it is the `state` record, which is bound to the browser and single use.
-/

public section

namespace Authentication.Oidc

/-- The `sub` of a provider that numbers its people. GitHub's `id` is stable across a rename of
the login, which the login is not, so the identity is keyed on the number (AUTH-6.6). -/
private def subjectOf (profile : Json) : Option String :=
  match (profile.getObjVal? "id").toOption with
  | some (.num n) => some (toString n)
  | some (.str s) => some s
  | _ => none

/--
The address to sign in with, out of a list the provider returns.

Only a verified one is a candidate, which is AUTH-6.7 applied where the provider reports it rather
than where a token claims it, and the primary is preferred among them so that somebody with
several gets the one they would expect. An account with no verified address yields none, and the
sign-in is refused rather than falling back to an unverified one.
-/
private def verifiedAddress (addresses : Json) : Option (String × Bool) :=
  match addresses with
  | .arr entries =>
    let verified := entries.toList.filterMap fun entry =>
      match (entry.getObjVal? "email").toOption.bind (·.getStr?.toOption),
        (entry.getObjVal? "verified").toOption.bind (·.getBool?.toOption) with
      | some address, some true =>
        some (address, ((entry.getObjVal? "primary").toOption.bind (·.getBool?.toOption)).getD false)
      | _, _ => none
    match verified.find? (·.2) with
    | some primary => some primary
    | none => verified.head?
  | _ => none

private def authorized (token : String) : Leancurl.Headers :=
  [ ("Authorization", "Bearer " ++ token)
  , ("Accept", "application/vnd.github+json")
  , ("User-Agent", "lean-authentication") ]

/--
The non-OIDC implementation of the seam.

The two URLs are configuration rather than discovery, because a provider with no metadata document
publishes nowhere to find them (AUTH-6.9). A provider configured as `discovered` reaches here only
by misconfiguration, and is refused rather than guessed at.
-/
def oauth2Identities (http : Fetch.Http IO) (tokens : TokenEndpoint IO) (secrets : ClientSecrets IO)
    (limits : Fetch.Limits := {}) : ProviderIdentities IO where
  redeem tenant provider discovery code redirectUri verifier _nonce now := do
    match provider.endpoints with
    | .discovered => pure (.error (.badDocument "endpoints"))
    | .configured _ _ profileUrl emailsUrl =>
      match ← secrets.produce tenant provider discovery now with
      | .error reason => pure (.error reason)
      | .ok secret =>
        match ← tokens.exchange discovery provider code redirectUri verifier secret with
        | .error reason => pure (.error reason)
        | .ok accessToken =>
          match ← Fetch.get http limits profileUrl (authorized accessToken) with
          | .error reason => pure (.error (.fetch reason))
          | .ok profileDocument =>
            match Json.parse profileDocument.body with
            | .error _ => pure (.error (.badDocument "profile"))
            | .ok profile =>
              match subjectOf profile with
              | none => pure (.error .subjectMissing)
              | some subject =>
                match ← Fetch.get http limits emailsUrl (authorized accessToken) with
                | .error reason => pure (.error (.fetch reason))
                | .ok emailDocument =>
                  match Json.parse emailDocument.body with
                  | .error _ => pure (.error (.badDocument "emails"))
                  | .ok addresses =>
                    match (verifiedAddress addresses).bind
                        (fun (raw, _) => (EmailAddress.parse raw).toOption) with
                    | none => pure (.error (.badDocument "email"))
                    | some address =>
                      pure (.ok
                        { identity := ⟨provider.issuer, subject⟩
                          address := some address
                          -- Only verified addresses reach here, so this is not a claim being
                          -- taken on trust: it is what the filter above already established.
                          addressVerified := true
                          hostedDomain := none })

end Authentication.Oidc
