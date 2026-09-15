# Changelog

## [Unreleased]

- `Service.Outcome` carries the code the cross-device page shows, derived under the pepper the attempt was minted with rather than the current one, which after a rotation revealed a code the attempt then refused (AUTH-5.2.2, AUTH-15.7.2); `Service.revealedCode` names that pepper.
- The anti-forgery token on the sign-in forms and on the OAuth consent form is accepted under any pepper still inside its overlap window, so a rotation no longer refuses every form in flight (AUTH-14.1.4, AUTH-15.7.2).

## [0.16.4] - 2026-09-15

- `Oidc.TokenEndpoint.exchange` answers `ProviderTokens` rather than a bare token, so the exchange no longer assumes an ID token: it read `id_token` alone, which refused every sign-in through a provider that is not OpenID Connect (AUTH-6.9).

## [0.16.3] - 2026-09-15

- `OidcHttp.Config.observeRefusal` is handed every refusal the federated routes answer with, and the tenant and provider it was for, because the page they render will never say which one it was (AUTH-14.2.6).
- `LinkFailure.name` is the operator's name for a refused link, as the refusals around it already had.
- `Service.identify` answers `Except SessionRejection` rather than `Option`, so a cookie nothing matches, a revoked session and each of the two timeouts are told apart. `Store.sessionByDigest` reports the same, and `Session.identify` is now `Session.rejection`.
- `Oidc.beginFederated` answers `Except StartRefusal`, which tells a throttled start from a random source that has stopped answering.

## [0.16.2] - 2026-09-14

- An identity can be linked to the account already signed in, which is the only way in for a provider that discloses no address an account could match, such as Apple's private relay (AUTH-6.7.1). `POST` the federated start; the account comes from the session and never from the request.
- `Service.linkIdentity` is the same operation without the flow, and `FederationState` carries the account it was begun for.
- Linking and unlinking an identity are recorded in the audit log, which AUTH-14.1.7 always required and neither did.

## [0.16.1] - 2026-09-14

- `StoredSecret.render` and `StoredSecret.parse` are the text form a sealed provider secret is configured as (AUTH-15.7.3.2). Without them a deployment whose configuration lives outside the binary had nowhere to put one.

## [0.16.0] - 2026-09-14

- Federated sign-in (§6), in three new targets: `AuthenticationFetch`, `AuthenticationOidc` and `AuthenticationOidcHttp`. OpenID Connect providers, Apple, and providers that are neither.
- Beginning a federated sign-in is rate limited, and the discovery document is cached (AUTH-14.1.1, AUTH-6.4). `LimitAction` gains `federatedStart`.
- `Oidc.identities` picks the right implementation per provider, so one tenant may offer OpenID Connect and non-OIDC providers at once.
- `Service.unlinkIdentity` removes a linked identity and refuses to leave an account with no way in (AUTH-6.8); `Service.linkedIdentities` lists them.
- An invitation can be completed with a provider, where it asserts the invited address (AUTH-8.6).
- `Credential` carries a typed descriptor, `AuthStore` gains linked identities, verified addresses and the state record of AUTH-6.2, and `Authentication.OAuth.Pkce` is now `Authentication.Pkce`.

## [0.15.2] - 2026-09-09

On leancrypto 0.4.0.

## [0.15.1] - 2026-09-08

Update dependencies.

## [0.15.0] - 2026-08-30

A refusal has an operator-facing name for a log record or a span attribute (`AccessToken.Rejection.name`, `GrantRejection.name`, `MetadataRejection.name`, `SignInRefusal.name`).

## [0.14.1] - 2026-08-30

Tidyups.

## [0.14.0] - 2026-08-29

`OAuth.Service.revoke` writes only where there is something to withdraw.

## [0.13.0] - 2026-08-29

- A refusal is available as a JSON document (`Service.refusalDocument`) as well as a header.
- A consent page's scope checkboxes have a field name that survives whatever the client put in the scope (`Scope.approvalField`, `Scope.approved`).
- A client that named no scopes can be offered the deployment's own set (`ConsentPrompt.withDefaultScopes`).
- Query and form parameters are read without losing the duplicates §4.1.1 refuses (`Params.ofQuery`).
- The authorisation server's four endpoints are shipped as routes (`OAuth.Http.routes`, `OAuth.Http.handler`), with a replaceable consent page (`OAuthPages`) and a mount that the metadata document's URL follows (`OAuthConfig.atOrigin`).

## [0.12.0] - 2026-08-26

`metadataDocument` takes the fetcher, not `Ports`

## [0.11.0] - 2026-08-26

Metadata now consistent with a client's true capabilities

## [0.10.0] - 2026-08-26

- An account can be shown what it has connected.
- Credentials that permit nothing are no longer granted.
- A code issued from a consent decision is bound to what the page displayed, not what the request said.

## [0.9.1] - 2026-08-25

Stop percent triplets in a redirect target being encoded a second time.

## [0.9.0] - 2026-08-25

- Percent-encode redirect targets in the `Location` header.
- Stop `returnTo` being dropped on same-device magic links.

## [0.8.0] - 2026-08-24

OAuth 2.1 authorisation server.

## [0.7.0] - 2026-08-22

Fix the development workflow for Safari.

## [0.6.0] - 2026-08-22

Shared connection pool.

## [0.5.0] - 2026-08-21

Trim trailing `/` from `baseUrl`.

## [0.4.0] - 2026-08-21

Switch to `lean-json`.

## [0.3.0] - 2026-08-20

- SQL pool support.
- Development email transport.
- Configurable tenant cookie session path.

## [0.2.0] - 2026-08-20

Switch to module system.

## [0.1.0] - 2026-08-20

Initial release.
