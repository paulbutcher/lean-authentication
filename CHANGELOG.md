# Changelog

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
