/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

/-!
One attestation object from the tests of py_webauthn, https://github.com/duo-labs/py_webauthn, at
commit d72e0f53cb6684fdd2f178bae83aeab8bda64665. It was captured from a real authenticator, which
is what makes it evidence that this library reads the layout devices emit rather than the layout
it writes itself.

`none` is the only attestation format this library accepts, so it is the only capture reproduced
here; the rest, including the packed and TPM formats, exercise the decoding and live in
`lean-cbor`.

Redistributed under py_webauthn's licence:

Copyright (c) 2017-2021 Duo Security, Inc. All rights reserved.

Redistribution and use in source and binary forms, with or without
modification, are permitted provided that the following conditions
are met:

1. Redistributions of source code must retain the above copyright
   notice, this list of conditions and the following disclaimer.
2. Redistributions in binary form must reproduce the above copyright
   notice, this list of conditions and the following disclaimer in the
   documentation and/or other materials provided with the distribution.
3. Neither the name of the copyright holder nor the names of its
   contributors may be used to endorse or promote products derived from
   this software without specific prior written permission.

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS
IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO,
THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR
PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR
CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL,
EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO,
PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR
PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF
LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
-/

public section

namespace Tests.Fixtures.PyWebauthn

/-- The relying party the capture was registered against, which `tests/test_verify_registration_response.py`
uses throughout. That `Leancrypto.Sha256.hash` of it equals the hash inside the capture is the
check that says the hash is where this library looks for it. -/
def relyingPartyId : String := "localhost"

/-- From `tests/test_verify_registration_response.py`, `test_verifies_none_attestation_response`,
base64url as py_webauthn records it. -/
def noneAttestation : String :=
    "o2NmbXRkbm9uZWdhdHRTdG10oGhhdXRoRGF0YVjESZYN5YgOjGh0NBcPZHZgW4_krrmihjLHmVzzuoMdl2NFAAAAFwAA\
    AAAAAAAAAAAAAAAAAAAAQPctcQPE5oNRRJk_nO_371mf7qE7qIodzr0eOf6ACvnMB1oQG165dqutoi1U44shGezu5_gk\
    TjmOPeJO0N8a7P-lAQIDJiABIVggSFbUJF-42Ug3pdM8rDRFu_N5oiVEysPDB6n66r_7dZAiWCDUVnB39FlGypL-qAoI\
    O9xWHtJygo2jfDmHl-_eKFRLDA"

end Tests.Fixtures.PyWebauthn
