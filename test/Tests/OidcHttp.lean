/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import AuthenticationOidcHttp

/-!
The federated routes (§6).

The path the provider is told to send the browser back to, and the path the routes answer on, are
built independently. A disagreement between them is the failure nothing observes until a real
provider redirects: everything works except the half of the flow that comes back.
-/

namespace Tests.OidcHttp
open Authentication Authentication.OidcHttp

private def base : BaseUrl := ⟨"https://auth.example.test"⟩

/-- A route capture standing where a tenant identifier goes, so what is compared is that the
tenant segment falls in the same place on both sides. A real tenant name would compare a path
against a copy of itself and pass whatever the table said. -/
private def anyTenant : TenantId := ⟨":tenant:String"⟩

private def anyProvider : ProviderId := ⟨":provider:String"⟩

private def configFor (tenant : TenantId) : TenantConfig tenant :=
  { displayName := "Acme"
    baseUrl := base
    sendingIdentity :=
      { address := (EmailAddress.parse "s@auth.example.test").toOption.getD default
        displayName := "Acme" }
    signupPolicy := .unrestricted }

/--
The URI the provider is given is the URI the callback route answers on.

`Routing.renderPattern` prints the declared route as the path it matches, and `callbackUri` is
what `beginFederated` puts in the authorization request and what the token request repeats. Both
sides carry captures rather than names, so what is established is that the tenant and the provider
segments fall in the same places, which is the part a table could get wrong while every path
built from one configuration still agreed with itself.

The left-hand side drops the origin, because a pattern matches a path and `callbackUri` returns an
absolute URL; `base` is a constant here and the origin is `BaseUrl.url`'s to prepend.
-/
theorem callbackPathAgrees :
    base.origin ++ Routing.renderPattern Federated.patterns.callback =
      callbackUri (configFor anyTenant) anyProvider := by decide

/-- The start route is the callback's path without its last segment, which is what makes the pair
readable as one place rather than two. -/
theorem startPathAgrees :
    Routing.renderPattern Federated.patterns.callback =
      Routing.renderPattern Federated.patterns.start ++ "/callback" := by decide

end Tests.OidcHttp
