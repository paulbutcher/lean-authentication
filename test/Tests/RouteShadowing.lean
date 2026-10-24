/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import AuthenticationHttp
import AuthenticationOidcHttp
import AuthenticationPasskeyHttp

/-!
Compiling is passing. `Routing.toHandler` checks for shadowing by reducing the route list it is
given, which it can do here only if each library table's body crosses the module boundary. A
`module` because a plain file sees every body whether or not it is exposed, and over any engine
because that is the most a consumer's table can leave unknown.
-/

namespace Tests.RouteShadowing
open Authentication Routing

variable {e : Engine} [ServerEngine e]

def appRoutes : List (Route (Result e)) :=
  [ .get [.lit "app" (by decide)] (fun _ => e.text Std.Http.Response.ok "app") ]

def combined [Clock IO] [RandomBytes IO] (http : Http.Config) (oidc : OidcHttp.Config)
    (passkey : PasskeyHttp.Config) : StatelessHandler e :=
  toHandler (Http.routes http ++ OidcHttp.routes oidc ++ PasskeyHttp.routes passkey ++ appRoutes)
    (fun _ => e.text Std.Http.Response.notFound "")

def perTenantOAuth [Clock IO] [RandomBytes IO] (config : OAuth.Http.Config) :
    StatelessHandler e :=
  toHandler ((OAuth.Http.routes config).browser ++ appRoutes)
    (fun _ => e.text Std.Http.Response.notFound "")

-- The tenant is a variable: only the mount's constructor has to be known.
def atOriginOAuth [Clock IO] [RandomBytes IO] {tenant : TenantId}
    (config : OAuth.Http.Config (.origin tenant)) : StatelessHandler e :=
  toHandler ((OAuth.Http.routes config).client ++ appRoutes)
    (fun _ => e.text Std.Http.Response.notFound "")

end Tests.RouteShadowing
