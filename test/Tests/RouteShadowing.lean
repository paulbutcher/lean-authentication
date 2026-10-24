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
`module` because a plain file sees every body whether or not it is exposed.
-/

namespace Tests.RouteShadowing
open Authentication Routing

def appRoutes : List (Route Result) :=
  [ .get [.lit "app" (by decide)] (fun _ => Std.Http.Response.ok.text "app") ]

def combined [Clock IO] [RandomBytes IO] (http : Http.Config) (oidc : OidcHttp.Config)
    (passkey : PasskeyHttp.Config) : Std.Http.Server.StatelessHandler :=
  toHandler (Http.routes http ++ OidcHttp.routes oidc ++ PasskeyHttp.routes passkey ++ appRoutes)
    (fun _ => Std.Http.Response.notFound.text "")

def perTenantOAuth [Clock IO] [RandomBytes IO] (config : OAuth.Http.Config) :
    Std.Http.Server.StatelessHandler :=
  toHandler ((OAuth.Http.routes config).browser ++ appRoutes)
    (fun _ => Std.Http.Response.notFound.text "")

-- The tenant is a variable: only the mount's constructor has to be known.
def atOriginOAuth [Clock IO] [RandomBytes IO] {tenant : TenantId}
    (config : OAuth.Http.Config (.origin tenant)) : Std.Http.Server.StatelessHandler :=
  toHandler ((OAuth.Http.routes config).client ++ appRoutes)
    (fun _ => Std.Http.Response.notFound.text "")

end Tests.RouteShadowing
