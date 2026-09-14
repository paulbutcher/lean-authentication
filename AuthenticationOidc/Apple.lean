/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import AuthenticationOidc.SignIn

/-!
The client secret Apple asks for (AUTH-6.9).

Apple does not issue a secret to hold. It issues a key, and what the token request carries is an
assertion signed with it, minted for this request and expiring shortly after. So this is the one
credential in the library that is produced rather than looked up, and the reason `ClientSecrets`
is a port at all.
-/

public section

namespace Authentication.Oidc

/-- How long a minted assertion is good for. Apple permits months; minutes is what a secret used
once and thrown away needs, and it bounds what a copy of one is worth. -/
def assertionLifetime : Duration := Duration.minutes 5

private def part (text : String) : String :=
  Leancrypto.Codec.Base64Url.encodeString text.toUTF8

/--
One `client_secret_jwt`, signed ES256 (AUTH-6.9).

`aud` is the provider's issuer rather than its token endpoint: Apple checks the assertion against
the issuer it publishes, and taking it from the discovery document means the two cannot disagree
with what AUTH-6.5 already validates ID tokens against.
-/
def mintAssertion (provider : ProviderConfig) (discovery : Discovery) (teamId keyId : String)
    (key : ByteArray) (now : Timestamp) : IO (Except OidcError String) := do
  -- Apple ships the key as a `.p8` file, which is PEM-armoured PKCS#8, so that is what a
  -- deployment has to seal and what arrives here.
  match ← Jose.Libcrypto.PreparedKey.ofPem ((String.fromUTF8? key).getD "") with
  | .error reason => pure (.error (.token reason))
  | .ok prepared =>
    let expiry := now.advance assertionLifetime
    let header := part ("{\"alg\":\"ES256\",\"kid\":\"" ++ keyId ++ "\"}")
    let payload := part
      ("{\"iss\":\"" ++ teamId ++ "\",\"iat\":" ++ toString now.epochSeconds ++
        ",\"exp\":" ++ toString expiry.epochSeconds ++ ",\"aud\":\"" ++ discovery.issuer ++
        "\",\"sub\":\"" ++ provider.clientId ++ "\"}")
    let signingInput := header ++ "." ++ payload
    match ← Jose.Backend.libcrypto.sign .es256 prepared signingInput.toUTF8 with
    | .error reason => pure (.error (.token reason))
    | .ok signature =>
      pure (.ok (signingInput ++ "." ++ Leancrypto.Codec.Base64Url.encodeString signature))

/--
The shipped way to turn configured credentials into the secret a token request carries.

A held secret is resolved and handed over; a key is resolved and used to sign. Neither reaches
here in clear from configuration: both arrive through the `Secrets` port of AUTH-15.7.3, and what
this returns is the only plaintext either has.
-/
def clientSecrets (secrets : Secrets IO) : ClientSecrets IO where
  produce tenant provider discovery now := do
    match provider.credentials with
    | .clientSecret held =>
      match ← secrets.resolve { tenant, provider := provider.id, field := .clientSecret } held with
      | .error _ => pure (.error (.badDocument "client-secret"))
      | .ok bytes => pure (.ok ((String.fromUTF8? bytes).getD ""))
    | .signingKey teamId keyId held =>
      match ← secrets.resolve { tenant, provider := provider.id, field := .signingKey } held with
      | .error _ => pure (.error (.badDocument "signing-key"))
      | .ok key => mintAssertion provider discovery teamId keyId key now

end Authentication.Oidc
